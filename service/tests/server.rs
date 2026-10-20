//! End to end over TCP: responses equal a direct engine run, and the feed
//! carries the same batches.
mod common;

use std::{
    io::{Read, Write},
    net::TcpStream,
};
use vmatch_core::{Engine, Event};
use vmatch_service::{
    journal::SyncMode,
    server::{start, Config},
    wire::{decode_event, encode_command, event_eq, BATCH_HDR_LEN, EVT_LEN},
};

fn read_batch(s: &mut TcpStream) -> (u64, Vec<Event>) {
    let mut h = [0u8; BATCH_HDR_LEN];
    s.read_exact(&mut h).unwrap();
    let seq = u64::from_le_bytes(h[0..8].try_into().unwrap());
    let n = u32::from_le_bytes(h[8..12].try_into().unwrap()) as usize;
    let mut evs = Vec::with_capacity(n);
    for _ in 0..n {
        let mut r = [0u8; EVT_LEN];
        s.read_exact(&mut r).unwrap();
        evs.push(decode_event(&r).unwrap());
    }
    (seq, evs)
}

#[test]
fn tcp_round_trip_matches_engine() {
    let (ticks, cap) = (64, 128);
    let r = start(Config {
        order_addr: "127.0.0.1:0".into(),
        feed_addr: Some("127.0.0.1:0".into()),
        ticks,
        cap,
        journal: None,
        sync: SyncMode::NoSync,
        max_batch: 32,
        inbound_queue: 1024,
    })
    .unwrap();
    let mut feed = TcpStream::connect(r.feed_addr.unwrap()).unwrap();
    std::thread::sleep(std::time::Duration::from_millis(50));
    let mut c = TcpStream::connect(r.order_addr).unwrap();
    c.set_nodelay(true).unwrap();

    let mut eng = Engine::try_new(ticks, cap).unwrap();
    let mut g = common::Gen::new(11, ticks, 10);
    for i in 0..2_000u64 {
        let cmd = g.next();
        let mut want = Vec::new();
        eng.step(cmd, &mut want);
        c.write_all(&encode_command(&cmd)).unwrap();
        let (seq, got) = read_batch(&mut c);
        assert_eq!(seq, i);
        assert!(
            want.len() == got.len() && want.iter().zip(&got).all(|(a, b)| event_eq(a, b)),
            "cmd {i}"
        );
        let (fseq, fgot) = read_batch(&mut feed);
        assert_eq!(fseq, i);
        assert!(fgot.len() == got.len() && fgot.iter().zip(&got).all(|(a, b)| event_eq(a, b)));
        g.observe(&got);
    }
    // malformed frame closes the connection
    c.write_all(&[0xFFu8; 24]).unwrap();
    let mut buf = [0u8; 1];
    assert_eq!(c.read(&mut buf).unwrap_or(0), 0);
}
