//! In-process engine benchmark: per-command latency distribution and
//! single-thread throughput on a market-maker-style workload.
//!
//!   cargo run --release -p vmatch-service --example bench -- [commands] [resting]

use hdrhistogram::Histogram;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::time::Instant;
use vmatch_core::{Command, Engine, Event, OrdType, Side, Tif};

struct Load {
    rng: SmallRng,
    live: Vec<(u64, u32)>,
    mid: i64,
    ticks: u32,
}

impl Load {
    fn price(&mut self, side: Side, aggressive: bool) -> u32 {
        // passive orders 1..40 ticks behind mid; aggressive ones cross by 0..3
        let d = if aggressive { -self.rng.gen_range(0..4) } else { self.rng.gen_range(1..40) };
        let p = match side {
            Side::Buy => self.mid - d,
            Side::Sell => self.mid + d,
        };
        p.clamp(0, self.ticks as i64 - 1) as u32
    }

    fn next(&mut self) -> Command {
        if self.rng.gen_ratio(1, 1000) {
            self.mid = (self.mid + self.rng.gen_range(-2..=2)).clamp(100, self.ticks as i64 - 100);
        }
        let side = if self.rng.gen_bool(0.5) { Side::Buy } else { Side::Sell };
        let r = self.rng.gen_range(0..100);
        if r < 45 || self.live.is_empty() {
            let p = self.price(side, false);
            Command::New { side, ord_type: OrdType::Limit, tif: Tif::Gtc, price: p, qty: self.rng.gen_range(1..100) }
        } else if r < 55 {
            let p = self.price(side, true);
            let tif = if self.rng.gen_bool(0.7) { Tif::Ioc } else { Tif::Gtc };
            Command::New { side, ord_type: OrdType::Limit, tif, price: p, qty: self.rng.gen_range(1..300) }
        } else if r < 85 {
            let i = self.rng.gen_range(0..self.live.len());
            let (id, _) = self.live.swap_remove(i);
            Command::Cancel { id }
        } else {
            let i = self.rng.gen_range(0..self.live.len());
            let (id, p) = self.live.swap_remove(i);
            Command::Replace { id, price: p, qty: self.rng.gen_range(1..100), post_only: false }
        }
    }

    fn observe(&mut self, ev: &[Event], last_price: &mut u32) {
        for e in ev {
            match *e {
                Event::Accepted { price, .. } => *last_price = price,
                Event::Rested { id, .. } => self.live.push((id, *last_price)),
                _ => {}
            }
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let n: usize = args.next().map(|s| s.parse().unwrap()).unwrap_or(5_000_000);
    let resting: usize = args.next().map(|s| s.parse().unwrap()).unwrap_or(200_000);
    let ticks = 1 << 16;
    let cap = 1 << 22;
    let mut eng = Engine::try_new(ticks, cap).unwrap();
    let mut load = Load { rng: SmallRng::seed_from_u64(1), live: Vec::new(), mid: ticks as i64 / 2, ticks };
    let mut ev: Vec<Event> = Vec::with_capacity(4096);
    let mut lp = 0;

    // warm up: build a deep book
    while load.live.len() < resting {
        let side = if load.rng.gen_bool(0.5) { Side::Buy } else { Side::Sell };
        let p = load.price(side, false);
        let c = Command::New { side, ord_type: OrdType::Limit, tif: Tif::Gtc, price: p, qty: load.rng.gen_range(1..100) };
        ev.clear();
        eng.step(c, &mut ev);
        load.observe(&ev, &mut lp);
    }

    // pre-generate commands is impossible (ids depend on results), so the
    // generator runs inline; it is cheap relative to the engine.
    let mut hist = Histogram::<u64>::new_with_bounds(1, 10_000_000, 3).unwrap();
    let mut fills = 0usize;
    let t0 = Instant::now();
    for _ in 0..n {
        let c = load.next();
        ev.clear();
        let s = Instant::now();
        eng.step(c, &mut ev);
        let d = s.elapsed().as_nanos() as u64;
        hist.record(d.max(1)).unwrap();
        fills += ev.iter().filter(|e| matches!(e, Event::Fill { .. })).count();
        load.observe(&ev, &mut lp);
    }
    let el = t0.elapsed();

    // throughput without per-op timers
    let mut load2 = Load { rng: SmallRng::seed_from_u64(2), live: load.live.clone(), mid: load.mid, ticks };
    let t1 = Instant::now();
    for _ in 0..n {
        let c = load2.next();
        ev.clear();
        eng.step(c, &mut ev);
        load2.observe(&ev, &mut lp);
    }
    let el2 = t1.elapsed();

    println!("commands            {n}");
    println!("resting at start    {resting}");
    println!("fills               {fills}");
    println!("throughput          {:.2} M cmd/s (incl. load generator)", n as f64 / el2.as_secs_f64() / 1e6);
    println!("latency per step()  (timer overhead included, ~20ns)");
    for q in [0.5, 0.9, 0.99, 0.999, 0.9999] {
        println!("  p{:<7} {:>8} ns", q * 100.0, hist.value_at_quantile(q));
    }
    println!("  max      {:>8} ns", hist.max());
    println!("  mean     {:>8.0} ns   (loop wall {:.2}s)", hist.mean(), el.as_secs_f64());
}
