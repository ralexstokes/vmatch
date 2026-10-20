//! The sequencer: owns the engine, assigns command sequence numbers, journals
//! commands before releasing responses, and recovers by replay.

use crate::journal::{self, Header, SyncMode};
use crate::snapshot::Snapshot;
use std::io;
use std::path::Path;
use vmatch_core::{Command, Engine, Event};

pub struct Sequencer {
    engine: Engine,
    journal: Option<journal::Writer>,
    events: Vec<Event>,
    seq: u64,
    cap: u32,
    /// Set when a journal write fails: the journal may now hold commands that
    /// were never applied, so the sequencer refuses further work (fail-stop).
    poisoned: bool,
}

#[derive(Debug)]
pub enum OpenError {
    BadConfig,
    Journal(journal::JournalError),
}

impl From<journal::JournalError> for OpenError {
    fn from(e: journal::JournalError) -> Self {
        OpenError::Journal(e)
    }
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for OpenError {}

impl Sequencer {
    /// An engine with no journal (tests, benchmarks).
    pub fn in_memory(ticks: u32, cap: u32) -> Result<Self, OpenError> {
        let engine = Engine::try_new(ticks, cap).ok_or(OpenError::BadConfig)?;
        Ok(Sequencer { engine, journal: None, events: Vec::with_capacity(1024), seq: 0, cap, poisoned: false })
    }

    /// Create a fresh journal at `path`.
    pub fn create(path: &Path, ticks: u32, cap: u32, sync: SyncMode) -> Result<Self, OpenError> {
        let engine = Engine::try_new(ticks, cap).ok_or(OpenError::BadConfig)?;
        let w = journal::Writer::create(path, Header { ticks, cap }, sync)?;
        Ok(Sequencer { engine, journal: Some(w), events: Vec::with_capacity(1024), seq: 0, cap, poisoned: false })
    }

    /// Recover from an existing journal by deterministic replay. Returns the
    /// sequencer and the number of commands replayed.
    pub fn recover(path: &Path, ticks: u32, cap: u32, sync: SyncMode) -> Result<(Self, u64), OpenError> {
        let mut engine = Engine::try_new(ticks, cap).ok_or(OpenError::BadConfig)?;
        let (w, cmds) = journal::Writer::open(path, Header { ticks, cap }, sync)?;
        let mut events = Vec::with_capacity(1024);
        for c in &cmds {
            events.clear();
            engine.step(*c, &mut events);
        }
        let n = cmds.len() as u64;
        Ok((Sequencer { engine, journal: Some(w), events, seq: n, cap, poisoned: false }, n))
    }

    /// Recover from the snapshot at `snap` (if present and valid) plus the
    /// journal suffix after it; falls back to full replay otherwise. Returns
    /// the sequencer, the commands replayed, and whether a snapshot was used.
    pub fn recover_with_snapshot(journal_path: &Path, snap: &Path, ticks: u32, cap: u32, sync: SyncMode) -> Result<(Self, u64, bool), OpenError> {
        let (w, cmds) = journal::Writer::open(journal_path, Header { ticks, cap }, sync)?;
        let restored = Snapshot::read(snap)
            .filter(|s| s.ticks == ticks && s.cap == cap && s.applied <= cmds.len() as u64)
            .and_then(|s| s.restore().map(|e| (e, s.applied)));
        let used = restored.is_some();
        let (mut engine, start) = match restored {
            Some(x) => x,
            None => (Engine::try_new(ticks, cap).ok_or(OpenError::BadConfig)?, 0),
        };
        let mut events = Vec::with_capacity(1024);
        for c in &cmds[start as usize..] {
            events.clear();
            engine.step(*c, &mut events);
        }
        let n = cmds.len() as u64;
        Ok((Sequencer { engine, journal: Some(w), events, seq: n, cap, poisoned: false }, n - start, used))
    }

    /// Write a snapshot of the current state (after everything applied so far).
    pub fn snapshot(&self, path: &Path) -> io::Result<()> {
        Snapshot::capture(&self.engine, self.cap(), self.seq).write(path)
    }

    fn cap(&self) -> u32 {
        self.cap
    }

    pub fn engine(&self) -> &Engine {
        &self.engine
    }

    pub fn next_seq(&self) -> u64 {
        self.seq
    }

    /// Apply one command without journaling.
    pub fn apply(&mut self, cmd: Command) -> (u64, &[Event]) {
        self.events.clear();
        self.engine.step(cmd, &mut self.events);
        let s = self.seq;
        self.seq += 1;
        (s, &self.events)
    }

    /// Journal a batch (one write + at most one fsync), then apply each
    /// command and hand its events to `on_result`. If the journal write
    /// fails nothing is applied and the sequencer is poisoned: restart and
    /// recover from the journal.
    pub fn process_batch<F: FnMut(u64, &Command, &[Event])>(&mut self, cmds: &[Command], mut on_result: F) -> io::Result<()> {
        if self.poisoned {
            return Err(io::Error::other("sequencer poisoned by an earlier journal failure"));
        }
        if let Some(j) = self.journal.as_mut() {
            for c in cmds {
                j.append(c);
            }
            if let Err(e) = j.commit() {
                self.poisoned = true;
                return Err(e);
            }
        }
        for c in cmds {
            self.events.clear();
            self.engine.step(*c, &mut self.events);
            on_result(self.seq, c, &self.events);
            self.seq += 1;
        }
        Ok(())
    }
}
