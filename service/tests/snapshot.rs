//! Snapshot export/import: restoring a snapshot and replaying the journal
//! suffix behaves exactly like never having stopped; invalid snapshots are
//! rejected by the verified importer.
mod common;

use vmatch_core::{Command, Engine, Event, SOrder};
use vmatch_service::{journal::SyncMode, sequencer::Sequencer, snapshot::Snapshot, wire::event_eq};

fn tmp(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("vmatch-snap-{}-{name}", std::process::id()));
    let _ = std::fs::remove_file(&d);
    d
}

fn workload(seed: u64, ticks: u32, cap: u32, n: usize) -> Vec<Command> {
    let mut g = common::Gen::new(seed, ticks, 20);
    let mut s = Sequencer::in_memory(ticks, cap).unwrap();
    (0..n)
        .map(|_| {
            let c = g.next();
            let ev = s.apply(c).1.to_vec();
            g.observe(&ev);
            c
        })
        .collect()
}

fn run_all(e: &mut Engine, cmds: &[Command]) -> Vec<Event> {
    let mut out = Vec::new();
    for c in cmds {
        e.step(*c, &mut out);
    }
    out
}

fn same(a: &[Event], b: &[Event]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| event_eq(x, y))
}

#[test]
fn export_import_roundtrip_at_every_point() {
    for seed in 0..20 {
        let (ticks, cap) = (32, 48);
        let cmds = workload(seed, ticks, cap, 3_000);
        // reference: per-command events of one uninterrupted run
        let mut reference = Engine::try_new(ticks, cap).unwrap();
        let per_cmd: Vec<Vec<Event>> = cmds
            .iter()
            .map(|c| {
                let mut ev = Vec::new();
                reference.step(*c, &mut ev);
                ev
            })
            .collect();
        let mut e = Engine::try_new(ticks, cap).unwrap();
        for (i, c) in cmds.iter().enumerate() {
            if i % 37 == 0 {
                let snap = Snapshot::capture(&e, cap, i as u64);
                let mut r = snap.restore().expect("valid snapshot rejected");
                let end = (i + 300).min(cmds.len());
                let want: Vec<Event> = per_cmd[i..end].iter().flatten().copied().collect();
                assert!(
                    same(&run_all(&mut r, &cmds[i..end]), &want),
                    "seed {seed} at {i}"
                );
                // export of the restored engine is identical to the snapshot
                let r2 = snap.restore().unwrap();
                let again = Snapshot::capture(&r2, cap, i as u64);
                let key =
                    |v: &[SOrder]| v.iter().map(|o| (o.id, o.price, o.qty)).collect::<Vec<_>>();
                assert_eq!(key(&again.bids), key(&snap.bids));
                assert_eq!(key(&again.asks), key(&snap.asks));
                assert_eq!(again.free, snap.free);
                assert_eq!(again.next_seq, snap.next_seq);
            }
            let mut ev = Vec::new();
            e.step(*c, &mut ev);
        }
    }
}

#[test]
fn snapshot_plus_journal_suffix_equals_full_run() {
    let (ticks, cap) = (64, 256);
    let cmds = workload(77, ticks, cap, 20_000);
    let (a, b) = cmds.split_at(12_345);

    let mut reference = Engine::try_new(ticks, cap).unwrap();
    run_all(&mut reference, a);
    let want = run_all(&mut reference, b);

    let jp = tmp("journal");
    let sp = tmp("snap");
    {
        let mut s = Sequencer::create(&jp, ticks, cap, SyncMode::NoSync).unwrap();
        for chunk in a[..10_000].chunks(64) {
            s.process_batch(chunk, |_, _, _| {}).unwrap();
        }
        s.snapshot(&sp).unwrap();
        for chunk in a[10_000..].chunks(64) {
            s.process_batch(chunk, |_, _, _| {}).unwrap();
        }
    }
    let (mut s2, replayed, used) =
        Sequencer::recover_with_snapshot(&jp, &sp, ticks, cap, SyncMode::NoSync).unwrap();
    assert!(used);
    assert_eq!(replayed, (a.len() - 10_000) as u64);
    let mut got = Vec::new();
    s2.process_batch(b, |_, _, ev| got.extend_from_slice(ev))
        .unwrap();
    assert!(same(&want, &got));

    // a corrupted snapshot is ignored and recovery falls back to full replay
    let mut d = std::fs::read(&sp).unwrap();
    let mid = d.len() / 2;
    d[mid] ^= 1;
    std::fs::write(&sp, d).unwrap();
    drop(s2);
    let (_, replayed, used) =
        Sequencer::recover_with_snapshot(&jp, &sp, ticks, cap, SyncMode::NoSync).unwrap();
    assert!(!used);
    assert_eq!(replayed, cmds.len() as u64);
    let _ = std::fs::remove_file(&jp);
    let _ = std::fs::remove_file(&sp);
}

#[test]
fn importer_rejects_invalid_states() {
    let (ticks, cap) = (16, 8);
    let ok = |b: &[SOrder], a: &[SOrder], f: &[u32], ns: u64| {
        Engine::import(ticks, cap, &b.to_vec(), &a.to_vec(), &f.to_vec(), ns).is_some()
    };
    let o = |seq: u64, slot: u64, price: u32, qty: u64| SOrder {
        id: seq * vmatch_core::SLOT_SPACE + slot,
        price,
        qty,
    };
    // valid
    assert!(ok(
        &[o(0, 0, 5, 1), o(1, 1, 4, 1)],
        &[o(2, 2, 6, 3)],
        &[3, 4, 5, 6, 7],
        3
    ));
    // bids out of priority order
    assert!(!ok(&[o(0, 0, 4, 1), o(1, 1, 5, 1)], &[], &[], 3));
    // same price, later order first (time priority violated)
    assert!(!ok(&[o(1, 1, 5, 1), o(0, 0, 5, 1)], &[], &[], 3));
    // crossed book
    assert!(!ok(&[o(0, 0, 6, 1)], &[o(1, 1, 6, 1)], &[], 3));
    // slot used twice
    assert!(!ok(&[o(0, 0, 5, 1)], &[o(1, 0, 6, 1)], &[], 3));
    assert!(!ok(&[o(0, 0, 5, 1)], &[], &[0], 3));
    assert!(!ok(&[], &[], &[1, 1], 3));
    // slot out of range, price out of band, zero qty, seq from the future
    assert!(!ok(&[o(0, 9, 5, 1)], &[], &[], 3));
    assert!(!ok(&[o(0, 0, 16, 1)], &[], &[], 3));
    assert!(!ok(&[o(0, 0, 5, 0)], &[], &[], 3));
    assert!(!ok(&[o(5, 0, 5, 1)], &[], &[], 3));
    assert!(!ok(&[], &[], &[8], 3));
}
