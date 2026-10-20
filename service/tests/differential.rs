//! The compiled engine against the executable transcription of the model.
mod common;

use vmatch_core::{Engine, Event};
use vmatch_service::{oracle::Model, wire::event_eq};

fn run(seed: u64, ticks: u32, cap: u32, max_qty: u64, n: usize) {
    let mut eng = Engine::try_new(ticks, cap).unwrap();
    let mut model = Model::new(ticks, cap);
    let mut g = common::Gen::new(seed, ticks, max_qty);
    let mut e1: Vec<Event> = Vec::new();
    let mut e2: Vec<Event> = Vec::new();
    for i in 0..n {
        let c = g.next();
        e1.clear();
        e2.clear();
        eng.step(c, &mut e1);
        model.step(c, &mut e2);
        assert!(
            e1.len() == e2.len() && e1.iter().zip(&e2).all(|(a, b)| event_eq(a, b)),
            "seed {seed} step {i}: {c:?}\nengine: {e1:?}\nmodel:  {e2:?}"
        );
        assert_eq!(
            eng.best_bid(),
            model.bids.first().map(|o| o.price),
            "seed {seed} step {i}"
        );
        assert_eq!(
            eng.best_ask(),
            model.asks.first().map(|o| o.price),
            "seed {seed} step {i}"
        );
        g.observe(&e1);
    }
}

#[test]
fn small_book_many_seeds() {
    for seed in 0..200 {
        run(seed, 16, 24, 20, 3_000);
    }
}

#[test]
fn wide_band() {
    for seed in 0..10 {
        run(1000 + seed, 4096, 4096, 1000, 50_000);
    }
}

#[test]
fn tiny_capacity() {
    for seed in 0..100 {
        run(5000 + seed, 4, 2, 5, 2_000);
    }
}

#[test]
fn single_tick() {
    for seed in 0..50 {
        run(9000 + seed, 1, 8, 5, 2_000);
    }
}

#[test]
fn coverage_sanity() {
    // Make sure the generator actually exercises every path.
    let mut eng = Engine::try_new(64, 256).unwrap();
    let mut g = common::Gen::new(7, 64, 50);
    let mut ev = Vec::new();
    let mut counts = [0usize; 8];
    let mut reasons = std::collections::BTreeMap::new();
    for _ in 0..200_000 {
        let c = g.next();
        ev.clear();
        eng.step(c, &mut ev);
        for e in &ev {
            let k = match e {
                Event::Accepted { .. } => 1,
                Event::Fill { .. } => 2,
                Event::Rested { .. } => 3,
                Event::Expired { .. } => 4,
                Event::Cancelled { .. } => 5,
                Event::Reduced { .. } => 6,
                Event::Rejected { reason } => {
                    *reasons.entry(format!("{reason:?}")).or_insert(0usize) += 1;
                    7
                }
            };
            counts[k] += 1;
        }
        g.observe(&ev);
    }
    eprintln!("counts {counts:?} reasons {reasons:?}");
    assert!(counts[1..].iter().all(|&c| c > 100));
    assert!(reasons.len() >= 6, "{reasons:?}");
}
