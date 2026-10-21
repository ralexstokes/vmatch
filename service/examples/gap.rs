//! Worst-case best-level recovery: the best bid sits at the top of the band
//! and the only other bid at the bottom, so every time the best level empties
//! the engine must find the next non-empty level across the whole band.
//!
//!   cargo run --release -p vmatch-service --example gap -- [rounds] [ticks]

use hdrhistogram::Histogram;
use vmatch_core::{Command, Engine, Event, OrdType, Side, Tif, MAX_TICKS};

fn main() {
    let mut args = std::env::args().skip(1);
    let rounds: usize = args.next().map(|s| s.parse().unwrap()).unwrap_or(10_000);
    let ticks: u32 = args.next().map(|s| s.parse().unwrap()).unwrap_or(MAX_TICKS);
    let mut eng = Engine::try_new(ticks, 1024).unwrap();
    let mut ev: Vec<Event> = Vec::with_capacity(16);
    let new = |price| Command::New {
        side: Side::Buy,
        ord_type: OrdType::Limit,
        tif: Tif::Gtc,
        price,
        qty: 1,
    };
    eng.step(new(0), &mut ev);

    let mut hist = Histogram::<u64>::new_with_bounds(1, 1_000_000_000, 3).unwrap();
    for _ in 0..rounds {
        ev.clear();
        eng.step(new(ticks - 1), &mut ev);
        let id = match ev[0] {
            Event::Accepted { id, .. } => id,
            e => panic!("unexpected {e:?}"),
        };
        ev.clear();
        let s = std::time::Instant::now();
        eng.step(Command::Cancel { id }, &mut ev);
        hist.record((s.elapsed().as_nanos() as u64).max(1)).unwrap();
        assert_eq!(eng.best_bid(), Some(0));
    }

    println!("ticks               {ticks}");
    println!("rounds              {rounds}");
    println!(
        "cancel of the best level (next level is {} ticks away)",
        ticks - 1
    );
    for q in [0.5, 0.99, 0.9999] {
        println!("  p{:<7} {:>10} ns", q * 100.0, hist.value_at_quantile(q));
    }
    println!("  max      {:>10} ns", hist.max());
}
