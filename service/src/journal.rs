//! Write-ahead command journal.
//!
//! The engine is deterministic (proven: its state and events are a function of
//! the command log), so the journal records *commands*, not effects. A
//! command is durable before its response is released.
//!
//! File layout: a 16-byte header `"VMJ1" | version u32 | ticks u32 | cap u32`,
//! then 36-byte records `crc32 u32 | seq u64 | command [24]`, where the CRC
//! covers `seq` and the command bytes. Sequence numbers start at 0 and are
//! contiguous. A torn final record (crash mid-write) is detected and truncated
//! on open.

use crate::wire::{decode_command, encode_command, CMD_LEN};
use std::{
    fs::{File, OpenOptions},
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
};
use vmatch_core::Command;

pub const MAGIC: &[u8; 4] = b"VMJ1";
pub const VERSION: u32 = 1;
pub const HDR_LEN: usize = 16;
pub const REC_LEN: usize = 4 + 8 + CMD_LEN;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub ticks: u32,
    pub cap: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncMode {
    /// `fdatasync` once per batch before responses are released.
    Fsync,
    /// Write to the OS page cache only (survives process crash, not power loss).
    NoSync,
}

#[derive(Debug)]
pub enum JournalError {
    Io(io::Error),
    BadHeader,
    HeaderMismatch {
        found: Header,
        expected: Header,
    },
    /// A record in the middle of the file is corrupt (not just a torn tail).
    Corrupt {
        offset: u64,
    },
    BadCommand {
        seq: u64,
    },
    SeqGap {
        expected: u64,
        found: u64,
    },
}

impl From<io::Error> for JournalError {
    fn from(e: io::Error) -> Self {
        JournalError::Io(e)
    }
}

impl std::fmt::Display for JournalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for JournalError {}

fn encode_record(seq: u64, cmd: &Command, out: &mut Vec<u8>) {
    let c = encode_command(cmd);
    let mut h = crc32fast::Hasher::new();
    h.update(&seq.to_le_bytes());
    h.update(&c);
    out.extend_from_slice(&h.finalize().to_le_bytes());
    out.extend_from_slice(&seq.to_le_bytes());
    out.extend_from_slice(&c);
}

/// Contents of a journal on disk.
pub struct Contents {
    pub header: Header,
    pub commands: Vec<Command>,
    /// Byte length of the valid prefix (header + whole, valid records).
    pub valid_len: u64,
    /// Bytes of torn tail found after the valid prefix.
    pub torn_bytes: u64,
}

/// Read and validate a journal. Only a torn *final* record is tolerated; any
/// other damage is an error.
pub fn read(path: &Path) -> Result<Contents, JournalError> {
    let mut f = File::open(path)?;
    let mut data = Vec::new();
    f.read_to_end(&mut data)?;
    if data.len() < HDR_LEN
        || &data[0..4] != MAGIC
        || u32::from_le_bytes(data[4..8].try_into().unwrap()) != VERSION
    {
        return Err(JournalError::BadHeader);
    }
    let header = Header {
        ticks: u32::from_le_bytes(data[8..12].try_into().unwrap()),
        cap: u32::from_le_bytes(data[12..16].try_into().unwrap()),
    };
    let mut commands = Vec::new();
    let mut off = HDR_LEN;
    while off + REC_LEN <= data.len() {
        let rec = &data[off..off + REC_LEN];
        let crc = u32::from_le_bytes(rec[0..4].try_into().unwrap());
        let mut h = crc32fast::Hasher::new();
        h.update(&rec[4..]);
        if h.finalize() != crc {
            // A bad CRC is only acceptable as the very last record (torn write).
            if off + REC_LEN == data.len() {
                break;
            }
            return Err(JournalError::Corrupt { offset: off as u64 });
        }
        let seq = u64::from_le_bytes(rec[4..12].try_into().unwrap());
        if seq != commands.len() as u64 {
            return Err(JournalError::SeqGap {
                expected: commands.len() as u64,
                found: seq,
            });
        }
        let cmd_bytes: &[u8; CMD_LEN] = rec[12..].try_into().unwrap();
        let cmd = decode_command(cmd_bytes).map_err(|_| JournalError::BadCommand { seq })?;
        commands.push(cmd);
        off += REC_LEN;
    }
    Ok(Contents {
        header,
        commands,
        valid_len: off as u64,
        torn_bytes: (data.len() - off) as u64,
    })
}

pub struct Writer {
    file: File,
    buf: Vec<u8>,
    next_seq: u64,
    sync: SyncMode,
}

impl Writer {
    /// Create a new journal, failing if the file exists.
    pub fn create(path: &Path, header: Header, sync: SyncMode) -> Result<Self, JournalError> {
        let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
        let mut h = Vec::with_capacity(HDR_LEN);
        h.extend_from_slice(MAGIC);
        h.extend_from_slice(&VERSION.to_le_bytes());
        h.extend_from_slice(&header.ticks.to_le_bytes());
        h.extend_from_slice(&header.cap.to_le_bytes());
        file.write_all(&h)?;
        file.sync_all()?;
        Ok(Writer {
            file,
            buf: Vec::with_capacity(1 << 16),
            next_seq: 0,
            sync,
        })
    }

    /// Open an existing journal for appending after recovery: validates it,
    /// truncates a torn tail, and returns the commands to replay.
    pub fn open(
        path: &Path,
        expected: Header,
        sync: SyncMode,
    ) -> Result<(Self, Vec<Command>), JournalError> {
        let c = read(path)?;
        if c.header != expected {
            return Err(JournalError::HeaderMismatch {
                found: c.header,
                expected,
            });
        }
        let mut file = OpenOptions::new().write(true).open(path)?;
        if c.torn_bytes > 0 {
            file.set_len(c.valid_len)?;
            file.sync_all()?;
        }
        file.seek(SeekFrom::Start(c.valid_len))?;
        let next_seq = c.commands.len() as u64;
        Ok((
            Writer {
                file,
                buf: Vec::with_capacity(1 << 16),
                next_seq,
                sync,
            },
            c.commands,
        ))
    }

    pub fn next_seq(&self) -> u64 {
        self.next_seq
    }

    /// Stage a command; returns its sequence number. Not durable until `commit`.
    pub fn append(&mut self, cmd: &Command) -> u64 {
        let seq = self.next_seq;
        encode_record(seq, cmd, &mut self.buf);
        self.next_seq += 1;
        seq
    }

    /// Write all staged records and, in `Fsync` mode, make them durable.
    pub fn commit(&mut self) -> io::Result<()> {
        if self.buf.is_empty() {
            return Ok(());
        }
        self.file.write_all(&self.buf)?;
        self.buf.clear();
        if self.sync == SyncMode::Fsync {
            self.file.sync_data()?;
        }
        Ok(())
    }
}
