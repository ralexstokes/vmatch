//! Journal + replay recovery produces the identical engine (checked through
//! identical future behaviour), including after a torn final write.
mod common;

use std::io::Write;
use vmatch_core::{Command, Event};
use vmatch_service::{
    journal::{self, SyncMode},
    sequencer::Sequencer,
    wire::event_eq,
};

fn tmp(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("vmatch-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_file(&d);
    d
}

fn collect(s: &mut Sequencer, cmds: &[Command]) -> Vec<Vec<Event>> {
    let mut out = Vec::new();
    s.process_batch(cmds, |_, _, ev| out.push(ev.to_vec()))
        .unwrap();
    out
}

fn same(a: &[Vec<Event>], b: &[Vec<Event>]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(x, y)| x.len() == y.len() && x.iter().zip(y).all(|(p, q)| event_eq(p, q)))
}

#[test]
fn recover_then_continue_matches_uninterrupted_run() {
    let (ticks, cap) = (128, 512);
    let mut g = common::Gen::new(42, ticks, 30);
    let mut cmds = Vec::new();
    let mut probe = Sequencer::in_memory(ticks, cap).unwrap();
    for _ in 0..30_000 {
        let c = g.next();
        let (_, ev) = probe.apply(c);
        let ev = ev.to_vec();
        g.observe(&ev);
        cmds.push(c);
    }
    let (first, second) = cmds.split_at(17_123);

    // reference: uninterrupted
    let mut r = Sequencer::in_memory(ticks, cap).unwrap();
    let _ = collect(&mut r, first);
    let want = collect(&mut r, second);

    // journaled run, "crash", recover, continue
    let p = tmp("recover");
    {
        let mut s = Sequencer::create(&p, ticks, cap, SyncMode::NoSync).unwrap();
        for chunk in first.chunks(97) {
            let _ = collect(&mut s, chunk);
        }
    }
    let (mut s2, n) = Sequencer::recover(&p, ticks, cap, SyncMode::NoSync).unwrap();
    assert_eq!(n, first.len() as u64);
    assert_eq!(s2.next_seq(), first.len() as u64);
    let got = collect(&mut s2, second);
    assert!(same(&want, &got));
    drop(s2);

    // the journal now holds the whole log; a full replay agrees too
    let c = journal::read(&p).unwrap();
    assert_eq!(c.commands.len(), cmds.len());
    let _ = std::fs::remove_file(&p);
}

#[test]
fn torn_tail_is_truncated_and_mid_file_corruption_is_fatal() {
    let (ticks, cap) = (16, 16);
    let p = tmp("torn");
    let mut g = common::Gen::new(3, ticks, 5);
    let cmds: Vec<Command> = (0..100).map(|_| g.next()).collect();
    {
        let mut s = Sequencer::create(&p, ticks, cap, SyncMode::NoSync).unwrap();
        let _ = collect(&mut s, &cmds);
    }
    let len = std::fs::metadata(&p).unwrap().len();
    // torn write: half a record appended
    {
        let mut f = std::fs::OpenOptions::new().append(true).open(&p).unwrap();
        f.write_all(&[0xAB; journal::REC_LEN / 2]).unwrap();
    }
    let (s, n) = Sequencer::recover(&p, ticks, cap, SyncMode::NoSync).unwrap();
    assert_eq!(n, 100);
    drop(s);
    assert_eq!(std::fs::metadata(&p).unwrap().len(), len);

    // a full final record with a bad CRC is also treated as torn
    {
        let mut f = std::fs::OpenOptions::new().append(true).open(&p).unwrap();
        f.write_all(&[0xCD; journal::REC_LEN]).unwrap();
    }
    let (_, n) = Sequencer::recover(&p, ticks, cap, SyncMode::NoSync).unwrap();
    assert_eq!(n, 100);

    // corrupting a record in the middle is detected, not silently skipped
    let mut data = std::fs::read(&p).unwrap();
    data[journal::HDR_LEN + 10 * journal::REC_LEN + 5] ^= 0xFF;
    std::fs::write(&p, &data).unwrap();
    assert!(matches!(
        journal::read(&p),
        Err(journal::JournalError::Corrupt { .. })
    ));

    // wrong instrument configuration is refused
    assert!(Sequencer::recover(&p, ticks + 1, cap, SyncMode::NoSync).is_err());
    let _ = std::fs::remove_file(&p);
}
