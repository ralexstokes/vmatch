use std::path::PathBuf;
use vmatch_service::journal::SyncMode;
use vmatch_service::server::{run, Config};

const USAGE: &str = "usage: vmatchd [--listen ADDR] [--feed ADDR] [--ticks N] [--capacity N]
               [--journal PATH] [--no-fsync] [--max-batch N]

  --listen    order-entry address           (default 127.0.0.1:9100)
  --feed      market-data/drop-copy address (default: disabled)
  --ticks     price band size: prices are 0..N (default 65536)
  --capacity  max resting orders            (default 1048576)
  --journal   write-ahead journal; replayed on start if it exists
  --no-fsync  don't fdatasync per batch (survives process crash only)
  --max-batch commands per journal commit   (default 256)";

fn main() {
    let mut cfg = Config {
        order_addr: "127.0.0.1:9100".into(),
        feed_addr: None,
        ticks: 65_536,
        cap: 1 << 20,
        journal: None,
        sync: SyncMode::Fsync,
        max_batch: 256,
        inbound_queue: 1 << 16,
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut val = || args.next().unwrap_or_else(|| die(&format!("missing value for {a}")));
        match a.as_str() {
            "--listen" => cfg.order_addr = val(),
            "--feed" => cfg.feed_addr = Some(val()),
            "--ticks" => cfg.ticks = val().parse().unwrap_or_else(|_| die("bad --ticks")),
            "--capacity" => cfg.cap = val().parse().unwrap_or_else(|_| die("bad --capacity")),
            "--journal" => cfg.journal = Some(PathBuf::from(val())),
            "--no-fsync" => cfg.sync = SyncMode::NoSync,
            "--max-batch" => cfg.max_batch = val().parse().unwrap_or_else(|_| die("bad --max-batch")),
            "-h" | "--help" => {
                println!("{USAGE}");
                return;
            }
            _ => die(&format!("unknown argument {a}")),
        }
    }
    if cfg.max_batch == 0 {
        die("--max-batch must be at least 1");
    }
    if let Err(e) = run(cfg) {
        eprintln!("vmatchd: {e}");
        std::process::exit(1);
    }
}

fn die(msg: &str) -> ! {
    eprintln!("vmatchd: {msg}\n\n{USAGE}");
    std::process::exit(2);
}
