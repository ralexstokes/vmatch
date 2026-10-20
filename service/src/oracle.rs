//! A direct, unoptimised transcription of the reference model (`spec.rs`)
//! into executable Rust. Used only for differential testing: it is an
//! independent check that the compiled engine behaves like the model it was
//! proven against (guarding against toolchain/erasure problems and against
//! misreading the specification).

use std::collections::VecDeque;
use vmatch_core::{Command, Event, OrdType, RejectReason, Side, Tif, MAX_QTY, MAX_SEQ, SLOT_SPACE};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Order {
    pub id: u64,
    pub price: u32,
    pub qty: u64,
}

#[derive(Clone, Debug)]
pub struct Model {
    pub ticks: u32,
    pub bids: Vec<Order>,
    pub asks: Vec<Order>,
    pub free: VecDeque<u32>,
    pub next_seq: u64,
}

fn idx(ticks: u32, side: Side, price: u32) -> i64 {
    match side {
        Side::Buy => ticks as i64 - 1 - price as i64,
        Side::Sell => price as i64,
    }
}

fn opp(s: Side) -> Side {
    match s {
        Side::Buy => Side::Sell,
        Side::Sell => Side::Buy,
    }
}

impl Model {
    pub fn new(ticks: u32, cap: u32) -> Self {
        Model {
            ticks,
            bids: vec![],
            asks: vec![],
            free: (0..cap).collect(),
            next_seq: 0,
        }
    }

    fn book(&mut self, s: Side) -> &mut Vec<Order> {
        match s {
            Side::Buy => &mut self.bids,
            Side::Sell => &mut self.asks,
        }
    }

    fn would_cross(&mut self, side: Side, price: u32) -> bool {
        let ms = opp(side);
        let lim = idx(self.ticks, ms, price);
        let t = self.ticks;
        let b = self.book(ms);
        !b.is_empty() && idx(t, ms, b[0].price) <= lim
    }

    fn fillable(&mut self, ms: Side, lim: i64) -> u128 {
        let t = self.ticks;
        self.book(ms)
            .iter()
            .take_while(|o| idx(t, ms, o.price) <= lim)
            .map(|o| o.qty as u128)
            .sum()
    }

    fn submit(&mut self, side: Side, price: u32, qty: u64, tif: Tif, out: &mut Vec<Event>) {
        let slot = self.free.pop_front().unwrap();
        let id = self.next_seq * SLOT_SPACE + slot as u64;
        out.push(Event::Accepted {
            id,
            side,
            price,
            qty,
        });
        let ms = opp(side);
        let lim = idx(self.ticks, ms, price);
        let mut rem = qty;
        loop {
            if rem == 0 {
                break;
            }
            let t = self.ticks;
            let m = match self.book(ms).first() {
                Some(m) if idx(t, ms, m.price) <= lim => *m,
                _ => break,
            };
            if m.qty <= rem {
                out.push(Event::Fill {
                    taker: id,
                    maker: m.id,
                    price: m.price,
                    qty: m.qty,
                });
                rem -= m.qty;
                self.book(ms).remove(0);
                self.free.push_front((m.id % SLOT_SPACE) as u32);
            } else {
                out.push(Event::Fill {
                    taker: id,
                    maker: m.id,
                    price: m.price,
                    qty: rem,
                });
                self.book(ms)[0].qty = m.qty - rem;
                rem = 0;
            }
        }
        let rest = rem > 0 && matches!(tif, Tif::Gtc | Tif::PostOnly);
        if rest {
            let t = self.ticks;
            let i = idx(t, side, price);
            let own = self.book(side);
            let pos = own
                .iter()
                .take_while(|o| idx(t, side, o.price) <= i)
                .count();
            own.insert(
                pos,
                Order {
                    id,
                    price,
                    qty: rem,
                },
            );
            out.push(Event::Rested { id, qty: rem });
        } else {
            if rem > 0 {
                out.push(Event::Expired { id, qty: rem });
            }
            self.free.push_front(slot);
        }
        self.next_seq += 1;
    }

    fn find(&self, id: u64) -> Option<(Side, usize)> {
        if let Some(j) = self.bids.iter().position(|o| o.id == id) {
            return Some((Side::Buy, j));
        }
        self.asks
            .iter()
            .position(|o| o.id == id)
            .map(|j| (Side::Sell, j))
    }

    fn remove_at(&mut self, side: Side, j: usize) -> Order {
        let o = self.book(side).remove(j);
        self.free.push_front((o.id % SLOT_SPACE) as u32);
        o
    }

    pub fn step(&mut self, c: Command, out: &mut Vec<Event>) {
        let rej = |out: &mut Vec<Event>, r| out.push(Event::Rejected { reason: r });
        match c {
            Command::New {
                side,
                ord_type,
                tif,
                price,
                qty,
            } => {
                let market = matches!(ord_type, OrdType::Market);
                let px = if market {
                    match side {
                        Side::Buy => self.ticks - 1,
                        Side::Sell => 0,
                    }
                } else {
                    price
                };
                let ms = opp(side);
                if market && !matches!(tif, Tif::Ioc | Tif::Fok) {
                    rej(out, RejectReason::InvalidTif)
                } else if !market && price >= self.ticks {
                    rej(out, RejectReason::InvalidPrice)
                } else if qty == 0 || qty > MAX_QTY {
                    rej(out, RejectReason::InvalidQty)
                } else if self.next_seq > MAX_SEQ {
                    rej(out, RejectReason::SeqExhausted)
                } else if self.free.is_empty() {
                    rej(out, RejectReason::BookFull)
                } else if matches!(tif, Tif::PostOnly) && self.would_cross(side, px) {
                    rej(out, RejectReason::WouldCross)
                } else if matches!(tif, Tif::Fok)
                    && self.fillable(ms, idx(self.ticks, ms, px)) < qty as u128
                {
                    rej(out, RejectReason::FokUnfillable)
                } else {
                    self.submit(side, px, qty, tif, out)
                }
            }
            Command::Cancel { id } => match self.find(id) {
                None => rej(out, RejectReason::UnknownOrder),
                Some((side, j)) => {
                    let o = self.remove_at(side, j);
                    out.push(Event::Cancelled { id, qty: o.qty });
                }
            },
            Command::Replace {
                id,
                price,
                qty,
                post_only,
            } => {
                if price >= self.ticks {
                    return rej(out, RejectReason::InvalidPrice);
                }
                if qty == 0 || qty > MAX_QTY {
                    return rej(out, RejectReason::InvalidQty);
                }
                let Some((side, j)) = self.find(id) else {
                    return rej(out, RejectReason::UnknownOrder);
                };
                let o = self.book(side)[j];
                if price == o.price && qty <= o.qty {
                    self.book(side)[j].qty = qty;
                    out.push(Event::Reduced {
                        id,
                        from: o.qty,
                        to: qty,
                    });
                } else if self.next_seq > MAX_SEQ {
                    rej(out, RejectReason::SeqExhausted)
                } else if post_only && self.would_cross(side, price) {
                    rej(out, RejectReason::WouldCross)
                } else {
                    self.remove_at(side, j);
                    out.push(Event::Cancelled { id, qty: o.qty });
                    let tif = if post_only { Tif::PostOnly } else { Tif::Gtc };
                    self.submit(side, price, qty, tif, out);
                }
            }
        }
    }
}
