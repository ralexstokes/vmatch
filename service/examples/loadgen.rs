//! TCP round-trip latency against a running vmatchd.
//!
//!   vmatchd --listen 127.0.0.1:9100 --journal /tmp/vm.journal &
//!   cargo run --release -p vmatch-service --example loadgen -- 127.0.0.1:9100 200000

use hdrhistogram::Histogram;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Instant;
use vmatch_core::{Command, OrdType, Side, Tif};
use vmatch_service::wire::{decode_event, encode_command, BATCH_HDR_LEN, EVT_LEN};

fn main() {
    let mut args = std::env::args().skip(1);
    let addr = args.next().unwrap_or_else(|| "127.0.0.1:9100".into());
    let n: usize = args.next().map(|s| s.parse().unwrap()).unwrap_or(100_000);
    let mut s = TcpStream::connect(&addr).expect("connect");
    s.set_nodelay(true).unwrap();
    let mut rng = SmallRng::seed_from_u64(9);
    let mut live: Vec<u64> = Vec::new();
    let mut hist = Histogram::<u64>::new_with_bounds(1, 1_000_000_000, 3).unwrap();
    let t0 = Instant::now();
    for _ in 0..n {
        let side = if rng.gen_bool(0.5) { Side::Buy } else { Side::Sell };
        let cmd = if live.len() > 1000 && rng.gen_bool(0.4) {
            Command::Cancel { id: live.swap_remove(rng.gen_range(0..live.len())) }
        } else {
            let p = 32_768 + match side {
                Side::Buy => -rng.gen_range(-2..40),
                Side::Sell => rng.gen_range(-2..40),
            };
            Command::New { side, ord_type: OrdType::Limit, tif: Tif::Gtc, price: p as u32, qty: rng.gen_range(1..100) }
        };
        let st = Instant::now();
        s.write_all(&encode_command(&cmd)).unwrap();
        let mut h = [0u8; BATCH_HDR_LEN];
        s.read_exact(&mut h).unwrap();
        let k = u32::from_le_bytes(h[8..12].try_into().unwrap()) as usize;
        for _ in 0..k {
            let mut r = [0u8; EVT_LEN];
            s.read_exact(&mut r).unwrap();
            if let Some(vmatch_core::Event::Rested { id, .. }) = decode_event(&r) {
                live.push(id);
            }
        }
        hist.record(st.elapsed().as_nanos() as u64).unwrap();
    }
    let el = t0.elapsed();
    println!("{n} round trips in {:.2}s ({:.0}/s, one outstanding)", el.as_secs_f64(), n as f64 / el.as_secs_f64());
    for q in [0.5, 0.9, 0.99, 0.999] {
        println!("  p{:<6} {:>9} ns", q * 100.0, hist.value_at_quantile(q));
    }
    println!("  max     {:>9} ns", hist.max());
}
