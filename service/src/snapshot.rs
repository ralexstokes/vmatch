//! Snapshot files: the engine's exported abstract state plus the number of
//! journaled commands it reflects. Restored through the verified
//! `Engine::import`, which re-checks every invariant, so a damaged or forged
//! snapshot can be rejected but never produce an ill-formed engine.
//!
//! Layout (little-endian): `"VMS1" | version u32 | ticks u32 | cap u32 |
//! applied u64 | next_seq u64 | n_bids u64 | n_asks u64 | n_free u64 |
//! bids (id u64, price u32, qty u64)* | asks (same)* | free u32* | crc32 u32`.
//! Written to a temporary file, fsynced, then atomically renamed.

use std::{
    fs::{self, File},
    io::{self, Read, Write},
    path::Path,
};
use vmatch_core::{Engine, SOrder};

pub const MAGIC: &[u8; 4] = b"VMS1";
pub const VERSION: u32 = 1;

pub struct Snapshot {
    pub ticks: u32,
    pub cap: u32,
    /// Number of journaled commands applied to reach this state.
    pub applied: u64,
    pub next_seq: u64,
    pub bids: Vec<SOrder>,
    pub asks: Vec<SOrder>,
    pub free: Vec<u32>,
}

impl Snapshot {
    pub fn capture(e: &Engine, cap: u32, applied: u64) -> Self {
        let mut bids = Vec::new();
        let mut asks = Vec::new();
        let mut free = Vec::new();
        let next_seq = e.export(&mut bids, &mut asks, &mut free);
        Snapshot {
            ticks: e.ticks(),
            cap,
            applied,
            next_seq,
            bids,
            asks,
            free,
        }
    }

    /// Rebuild an engine; `None` if the state violates any engine invariant.
    pub fn restore(&self) -> Option<Engine> {
        Engine::import(
            self.ticks,
            self.cap,
            &self.bids,
            &self.asks,
            &self.free,
            self.next_seq,
        )
    }

    fn encode(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(
            56 + 20 * (self.bids.len() + self.asks.len()) + 4 * self.free.len() + 4,
        );
        b.extend_from_slice(MAGIC);
        b.extend_from_slice(&VERSION.to_le_bytes());
        b.extend_from_slice(&self.ticks.to_le_bytes());
        b.extend_from_slice(&self.cap.to_le_bytes());
        for v in [
            self.applied,
            self.next_seq,
            self.bids.len() as u64,
            self.asks.len() as u64,
            self.free.len() as u64,
        ] {
            b.extend_from_slice(&v.to_le_bytes());
        }
        for o in self.bids.iter().chain(self.asks.iter()) {
            b.extend_from_slice(&o.id.to_le_bytes());
            b.extend_from_slice(&o.price.to_le_bytes());
            b.extend_from_slice(&o.qty.to_le_bytes());
        }
        for f in &self.free {
            b.extend_from_slice(&f.to_le_bytes());
        }
        let crc = crc32fast::hash(&b);
        b.extend_from_slice(&crc.to_le_bytes());
        b
    }

    fn decode(d: &[u8]) -> Option<Self> {
        if d.len() < 60 || &d[0..4] != MAGIC {
            return None;
        }
        let (body, tail) = d.split_at(d.len() - 4);
        if crc32fast::hash(body) != u32::from_le_bytes(tail.try_into().ok()?) {
            return None;
        }
        let u32_at = |i: usize| u32::from_le_bytes(body[i..i + 4].try_into().unwrap());
        let u64_at = |i: usize| u64::from_le_bytes(body[i..i + 8].try_into().unwrap());
        if u32_at(4) != VERSION {
            return None;
        }
        let (ticks, cap) = (u32_at(8), u32_at(12));
        let (applied, next_seq) = (u64_at(16), u64_at(24));
        let (nb, na, nf) = (
            u64_at(32) as usize,
            u64_at(40) as usize,
            u64_at(48) as usize,
        );
        let need = 56usize
            .checked_add(nb.checked_add(na)?.checked_mul(20)?)?
            .checked_add(nf.checked_mul(4)?)?;
        if body.len() != need {
            return None;
        }
        let mut off = 56;
        let mut orders = |n: usize| {
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(SOrder {
                    id: u64_at(off),
                    price: u32_at(off + 8),
                    qty: u64_at(off + 12),
                });
                off += 20;
            }
            v
        };
        let bids = orders(nb);
        let asks = orders(na);
        let free = (0..nf).map(|i| u32_at(off + 4 * i)).collect();
        Some(Snapshot {
            ticks,
            cap,
            applied,
            next_seq,
            bids,
            asks,
            free,
        })
    }

    /// Atomically write to `path` (via `path.tmp`, fsync, rename, fsync dir).
    pub fn write(&self, path: &Path) -> io::Result<()> {
        let tmp = path.with_extension("tmp");
        {
            let mut f = File::create(&tmp)?;
            f.write_all(&self.encode())?;
            f.sync_all()?;
        }
        fs::rename(&tmp, path)?;
        if let Some(dir) = path.parent() {
            if let Ok(d) = File::open(if dir.as_os_str().is_empty() {
                Path::new(".")
            } else {
                dir
            }) {
                let _ = d.sync_all();
            }
        }
        Ok(())
    }

    /// Read a snapshot; `None` if missing, truncated or failing its checksum.
    pub fn read(path: &Path) -> Option<Self> {
        let mut d = Vec::new();
        File::open(path).ok()?.read_to_end(&mut d).ok()?;
        Self::decode(&d)
    }
}
