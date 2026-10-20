//! Wire-independent types shared by the verified engine, its specification and
//! the (unverified) service shell.

use vstd::prelude::*;

verus! {

/// Number of low bits of an `OrderId` that hold the arena slot.
pub const SLOT_BITS: u64 = 24;
/// `2^SLOT_BITS`: ids are `seq * SLOT_SPACE + slot`.
pub const SLOT_SPACE: u64 = 16_777_216;
/// Largest sequence number that still yields an id that fits in a `u64`.
pub const MAX_SEQ: u64 = 1_099_511_627_775; // 2^40 - 1
/// Largest accepted order quantity (2^62). Keeps every partial sum the engine
/// forms strictly below `u64::MAX`.
pub const MAX_QTY: u64 = 4_611_686_018_427_387_904;
/// Largest arena capacity (number of order slots).
pub const MAX_CAPACITY: u32 = 16_777_216;
/// Largest number of price ticks in an instrument's band.
pub const MAX_TICKS: u32 = 16_777_216;
/// Null link in the arena.
pub const NIL: u32 = 0xffff_ffff;

#[derive(Clone, Copy, Debug)]
pub enum Side {
    Buy,
    Sell,
}

#[derive(Clone, Copy, Debug)]
pub enum Tif {
    /// Good-till-cancel: match, then rest the remainder.
    Gtc,
    /// Immediate-or-cancel: match, then expire the remainder.
    Ioc,
    /// Fill-or-kill: execute in full immediately or reject with no effect.
    Fok,
    /// Post-only (maker-only): reject if it would take liquidity, else rest.
    PostOnly,
}

#[derive(Clone, Copy, Debug)]
pub enum OrdType {
    Limit,
    /// Market orders carry no price; they are matched as limit orders at the
    /// extreme of the instrument's tick band and must be IOC or FOK.
    Market,
}

#[derive(Clone, Copy, Debug)]
pub enum Command {
    New { side: Side, ord_type: OrdType, tif: Tif, price: u32, qty: u64 },
    Cancel { id: u64 },
    /// Cancel/replace. Same price and a quantity no larger than the current
    /// remaining quantity reduces in place and keeps queue priority; anything
    /// else is an atomic cancel + new GTC (or post-only) order with a new id.
    Replace { id: u64, price: u32, qty: u64, post_only: bool },
}

#[derive(Clone, Copy, Debug)]
pub enum RejectReason {
    InvalidPrice,
    InvalidQty,
    InvalidTif,
    BookFull,
    SeqExhausted,
    UnknownOrder,
    WouldCross,
    FokUnfillable,
}

#[derive(Clone, Copy, Debug)]
pub enum Event {
    /// A new order entered the engine with this id.
    Accepted { id: u64, side: Side, price: u32, qty: u64 },
    /// `qty` traded at the resting (maker) order's price.
    Fill { taker: u64, maker: u64, price: u32, qty: u64 },
    /// The taker's remainder now rests on the book.
    Rested { id: u64, qty: u64 },
    /// The unfilled remainder of an IOC or market order was discarded.
    Expired { id: u64, qty: u64 },
    /// A resting order was removed with `qty` unfilled.
    Cancelled { id: u64, qty: u64 },
    /// A resting order's quantity was reduced in place, keeping priority.
    Reduced { id: u64, from: u64, to: u64 },
    /// The command had no effect.
    Rejected { reason: RejectReason },
}

/// A resting order as seen by the specification.
#[derive(Clone, Copy, Debug)]
pub struct SOrder {
    pub id: u64,
    pub price: u32,
    pub qty: u64,
}

pub open spec fn seq_of(id: u64) -> int {
    id as int / SLOT_SPACE as int
}

pub open spec fn slot_of(id: u64) -> int {
    id as int % SLOT_SPACE as int
}

pub open spec fn make_id(seq: u64, slot: u32) -> u64 {
    (seq as int * SLOT_SPACE as int + slot as int) as u64
}

pub open spec fn opp(side: Side) -> Side {
    match side {
        Side::Buy => Side::Sell,
        Side::Sell => Side::Buy,
    }
}

/// Priority index of a price on one side: smaller is better. Index 0 is the
/// highest bid / lowest ask.
pub open spec fn idx(ticks: u32, side: Side, price: u32) -> int {
    match side {
        Side::Buy => ticks as int - 1 - price as int,
        Side::Sell => price as int,
    }
}

pub open spec fn market_price(ticks: u32, side: Side) -> u32 {
    match side {
        Side::Buy => (ticks - 1) as u32,
        Side::Sell => 0,
    }
}

} // verus!
