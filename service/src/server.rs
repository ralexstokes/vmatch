//! TCP front end. One engine thread; one reader and one writer thread per
//! order-entry connection; a market-data/drop-copy feed that receives every
//! response batch.
//!
//! Order entry: clients send 24-byte command frames and receive one response
//! batch (header + events) per command, in order. A malformed frame closes
//! the connection. The feed port streams every batch for every command.

use crate::journal::SyncMode;
use crate::sequencer::Sequencer;
use crate::wire::{decode_command, encode_batch, CMD_LEN};
use std::collections::HashMap;
use std::io::{self, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::mpsc::{self, Receiver, Sender, SyncSender, TrySendError};
use std::thread;
use vmatch_core::Command;

pub struct Config {
    pub order_addr: String,
    pub feed_addr: Option<String>,
    pub ticks: u32,
    pub cap: u32,
    pub journal: Option<PathBuf>,
    pub sync: SyncMode,
    /// Most commands journaled and applied per batch.
    pub max_batch: usize,
    /// Bound on queued commands from all clients (backpressure).
    pub inbound_queue: usize,
}

enum Msg {
    Connect(u64, Sender<Vec<u8>>),
    Cmd(u64, Command),
    Disconnect(u64),
    Subscribe(SyncSender<std::sync::Arc<Vec<u8>>>),
}

pub struct Running {
    pub order_addr: std::net::SocketAddr,
    pub feed_addr: Option<std::net::SocketAddr>,
    pub engine: thread::JoinHandle<io::Result<()>>,
}

/// Recover (or create) state, bind the listeners and start the engine thread.
pub fn start(cfg: Config) -> io::Result<Running> {
    let mut seqr = match &cfg.journal {
        Some(p) if p.exists() => {
            let (s, n) = Sequencer::recover(p, cfg.ticks, cfg.cap, cfg.sync)
                .map_err(|e| io::Error::other(e.to_string()))?;
            eprintln!("vmatchd: recovered {n} commands from {}", p.display());
            s
        }
        Some(p) => Sequencer::create(p, cfg.ticks, cfg.cap, cfg.sync).map_err(|e| io::Error::other(e.to_string()))?,
        None => Sequencer::in_memory(cfg.ticks, cfg.cap).map_err(|e| io::Error::other(e.to_string()))?,
    };

    let (tx, rx) = mpsc::sync_channel::<Msg>(cfg.inbound_queue);

    let order_listener = TcpListener::bind(&cfg.order_addr)?;
    let order_addr = order_listener.local_addr()?;
    {
        let tx = tx.clone();
        thread::Builder::new().name("accept-orders".into()).spawn(move || accept_orders(order_listener, tx))?;
    }
    let mut feed_addr = None;
    if let Some(addr) = &cfg.feed_addr {
        let feed_listener = TcpListener::bind(addr)?;
        feed_addr = Some(feed_listener.local_addr()?);
        let tx = tx.clone();
        thread::Builder::new().name("accept-feed".into()).spawn(move || accept_feed(feed_listener, tx))?;
    }
    drop(tx);
    let max_batch = cfg.max_batch;
    let engine = thread::Builder::new().name("engine".into()).spawn(move || engine_loop(&mut seqr, rx, max_batch))?;
    Ok(Running { order_addr, feed_addr, engine })
}

/// Start and run until the engine thread stops.
pub fn run(cfg: Config) -> io::Result<()> {
    let r = start(cfg)?;
    eprintln!("vmatchd: order entry on {}", r.order_addr);
    if let Some(a) = r.feed_addr {
        eprintln!("vmatchd: feed on {a}");
    }
    r.engine.join().map_err(|_| io::Error::other("engine thread panicked"))?
}

fn accept_orders(l: TcpListener, tx: SyncSender<Msg>) {
    let mut next_id = 0u64;
    for stream in l.incoming() {
        let Ok(stream) = stream else { continue };
        let _ = stream.set_nodelay(true);
        let id = next_id;
        next_id += 1;
        let (wtx, wrx) = mpsc::channel::<Vec<u8>>();
        if tx.send(Msg::Connect(id, wtx)).is_err() {
            return;
        }
        let Ok(ws) = stream.try_clone() else { continue };
        let _ = thread::Builder::new().name(format!("conn-{id}-w")).spawn(move || writer(ws, wrx));
        let tx2 = tx.clone();
        let _ = thread::Builder::new().name(format!("conn-{id}-r")).spawn(move || reader(id, stream, tx2));
    }
}

fn reader(id: u64, stream: TcpStream, tx: SyncSender<Msg>) {
    let mut r = BufReader::with_capacity(1 << 16, stream);
    let mut frame = [0u8; CMD_LEN];
    loop {
        if r.read_exact(&mut frame).is_err() {
            break;
        }
        match decode_command(&frame) {
            Ok(cmd) => {
                if tx.send(Msg::Cmd(id, cmd)).is_err() {
                    return;
                }
            }
            Err(_) => break, // protocol error: drop the connection
        }
    }
    let _ = tx.send(Msg::Disconnect(id));
}

fn writer(mut stream: TcpStream, rx: Receiver<Vec<u8>>) {
    while let Ok(buf) = rx.recv() {
        if stream.write_all(&buf).is_err() {
            break;
        }
    }
    let _ = stream.shutdown(std::net::Shutdown::Both);
}

fn accept_feed(l: TcpListener, tx: SyncSender<Msg>) {
    for stream in l.incoming() {
        let Ok(mut stream) = stream else { continue };
        let _ = stream.set_nodelay(true);
        // Bounded: a subscriber that falls this far behind is dropped rather
        // than slowing the engine.
        let (ftx, frx) = mpsc::sync_channel::<std::sync::Arc<Vec<u8>>>(4096);
        if tx.send(Msg::Subscribe(ftx)).is_err() {
            return;
        }
        let _ = thread::Builder::new().name("feed-w".into()).spawn(move || {
            while let Ok(buf) = frx.recv() {
                if stream.write_all(&buf).is_err() {
                    break;
                }
            }
        });
    }
}

fn engine_loop(seqr: &mut Sequencer, rx: Receiver<Msg>, max_batch: usize) -> io::Result<()> {
    let mut conns: HashMap<u64, Sender<Vec<u8>>> = HashMap::new();
    let mut subs: Vec<SyncSender<std::sync::Arc<Vec<u8>>>> = Vec::new();
    let mut batch: Vec<(u64, Command)> = Vec::with_capacity(max_batch);
    let mut cmds: Vec<Command> = Vec::with_capacity(max_batch);
    let mut per_conn: HashMap<u64, Vec<u8>> = HashMap::new();
    let mut feed: Vec<u8> = Vec::with_capacity(1 << 16);

    let handle = |m: Msg, batch: &mut Vec<(u64, Command)>, conns: &mut HashMap<u64, Sender<Vec<u8>>>, subs: &mut Vec<_>| match m {
        Msg::Connect(id, s) => {
            conns.insert(id, s);
        }
        Msg::Disconnect(id) => {
            conns.remove(&id);
        }
        Msg::Subscribe(s) => subs.push(s),
        Msg::Cmd(id, c) => batch.push((id, c)),
    };

    loop {
        // Block for the first message, then drain without blocking.
        let Ok(first) = rx.recv() else { return Ok(()) };
        handle(first, &mut batch, &mut conns, &mut subs);
        while batch.len() < max_batch {
            match rx.try_recv() {
                Ok(m) => handle(m, &mut batch, &mut conns, &mut subs),
                Err(_) => break,
            }
        }
        if batch.is_empty() {
            continue;
        }
        cmds.clear();
        cmds.extend(batch.iter().map(|(_, c)| *c));
        feed.clear();
        let mut i = 0;
        seqr.process_batch(&cmds, |seq, _cmd, events| {
            let conn = batch[i].0;
            i += 1;
            encode_batch(seq, events, per_conn.entry(conn).or_default());
            encode_batch(seq, events, &mut feed);
        })?;
        for (conn, buf) in per_conn.iter_mut() {
            if buf.is_empty() {
                continue;
            }
            if let Some(s) = conns.get(conn) {
                let _ = s.send(std::mem::take(buf));
            } else {
                buf.clear();
            }
        }
        if !subs.is_empty() {
            let shared = std::sync::Arc::new(feed.clone());
            subs.retain(|s| match s.try_send(shared.clone()) {
                Ok(()) => true,
                Err(TrySendError::Full(_)) | Err(TrySendError::Disconnected(_)) => false,
            });
        }
        batch.clear();
    }
}
