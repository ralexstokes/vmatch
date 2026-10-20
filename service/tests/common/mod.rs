#![allow(dead_code)]
use rand::{rngs::SmallRng, RngExt, SeedableRng};
use vmatch_core::{Command, Event, OrdType, Side, Tif};

/// Random command generator that mostly targets live orders, with a mix of
/// every order type, edge-case quantities and invalid inputs.
pub struct Gen {
    pub rng: SmallRng,
    pub ticks: u32,
    pub live: Vec<u64>,
    pub info: std::collections::HashMap<u64, (u32, u64)>,
    pending_price: std::collections::HashMap<u64, u32>,
    pub mid: u32,
    pub max_qty: u64,
}

impl Gen {
    pub fn new(seed: u64, ticks: u32, max_qty: u64) -> Self {
        Gen {
            rng: SmallRng::seed_from_u64(seed),
            ticks,
            live: vec![],
            info: Default::default(),
            pending_price: Default::default(),
            mid: ticks / 2,
            max_qty,
        }
    }

    pub fn observe(&mut self, events: &[Event]) {
        for e in events {
            match *e {
                Event::Accepted { id, price, .. } => {
                    self.pending_price.insert(id, price);
                }
                Event::Rested { id, qty } => {
                    let p = self.pending_price.remove(&id).unwrap_or(0);
                    self.live.push(id);
                    self.info.insert(id, (p, qty));
                }
                Event::Cancelled { id, .. } => self.forget(id),
                Event::Fill { maker, qty, .. } => {
                    if let Some(x) = self.info.get_mut(&maker) {
                        x.1 -= qty.min(x.1);
                        if x.1 == 0 {
                            self.forget(maker);
                        }
                    }
                }
                Event::Reduced { id, to, .. } => {
                    if let Some(x) = self.info.get_mut(&id) {
                        x.1 = to;
                    }
                }
                _ => {}
            }
        }
        self.pending_price.clear();
    }

    fn forget(&mut self, id: u64) {
        self.info.remove(&id);
        if let Some(i) = self.live.iter().position(|&x| x == id) {
            self.live.swap_remove(i);
        }
    }

    fn price(&mut self) -> u32 {
        // random walk around a drifting mid, occasionally anywhere/invalid
        if self.rng.random_ratio(1, 50) {
            self.mid = self.rng.random_range(0..self.ticks);
        }
        let r = self.rng.random_range(0..100);
        if r < 2 {
            self.ticks + self.rng.random_range(0..3) // invalid
        } else if r < 5 {
            self.rng.random_range(0..self.ticks)
        } else {
            let w = 6i64;
            (self.mid as i64 + self.rng.random_range(-w..=w)).clamp(0, self.ticks as i64 - 1) as u32
        }
    }

    fn qty(&mut self) -> u64 {
        let r = self.rng.random_range(0..100);
        if r < 1 {
            0
        } else if r < 2 {
            vmatch_core::MAX_QTY + self.rng.random_range(0..2)
        } else if r < 3 {
            vmatch_core::MAX_QTY
        } else {
            self.rng.random_range(1..=self.max_qty)
        }
    }

    pub fn next(&mut self) -> Command {
        let r = self.rng.random_range(0..100);
        let side = if self.rng.random_bool(0.5) {
            Side::Buy
        } else {
            Side::Sell
        };
        if r < 55 {
            let (ord_type, tif) = match self.rng.random_range(0..100) {
                0..=59 => (OrdType::Limit, Tif::Gtc),
                60..=69 => (OrdType::Limit, Tif::Ioc),
                70..=77 => (OrdType::Limit, Tif::Fok),
                78..=87 => (OrdType::Limit, Tif::PostOnly),
                88..=93 => (OrdType::Market, Tif::Ioc),
                94..=97 => (OrdType::Market, Tif::Fok),
                _ => (
                    OrdType::Market,
                    if self.rng.random_bool(0.5) {
                        Tif::Gtc
                    } else {
                        Tif::PostOnly
                    },
                ),
            };
            Command::New {
                side,
                ord_type,
                tif,
                price: self.price(),
                qty: self.qty(),
            }
        } else if r < 80 {
            let id = self.pick_id();
            Command::Cancel { id }
        } else {
            let id = self.pick_id();
            if let (true, Some(&(p, q))) = (self.rng.random_bool(0.4), self.info.get(&id)) {
                // in-place reduction (keeps priority), sometimes to the same qty
                let nq = self.rng.random_range(1..=q);
                return Command::Replace {
                    id,
                    price: p,
                    qty: nq,
                    post_only: false,
                };
            }
            Command::Replace {
                id,
                price: self.price(),
                qty: self.qty(),
                post_only: self.rng.random_ratio(1, 5),
            }
        }
    }

    fn pick_id(&mut self) -> u64 {
        if !self.live.is_empty() && self.rng.random_ratio(19, 20) {
            let i = self.rng.random_range(0..self.live.len());
            self.live[i]
        } else {
            self.rng.random()
        }
    }
}
