//! The reference model: a deliberately simple, purely functional order book.
//!
//! Each side of the book is a single sequence of resting orders kept in
//! priority order (best price first; earlier arrival first within a price).
//! Matching always consumes from the front of the opposite sequence. The
//! optimised engine in `engine.rs` is proven to compute exactly `step` on the
//! abstraction of its state, so every theorem proven about this model in
//! `props.rs` holds for the engine.

use crate::types::*;
use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub struct SState {
    /// Size of the instrument's price band: valid prices are `0..ticks`.
    pub ticks: u32,
    pub bids: Seq<SOrder>,
    pub asks: Seq<SOrder>,
    /// Free order slots, as a stack (index 0 is the top).
    pub free: Seq<u32>,
    /// Sequence number the next accepted order will get.
    pub next_seq: u64,
}

pub open spec fn book(s: SState, side: Side) -> Seq<SOrder> {
    match side {
        Side::Buy => s.bids,
        Side::Sell => s.asks,
    }
}

pub open spec fn with_book(s: SState, side: Side, b: Seq<SOrder>) -> SState {
    match side {
        Side::Buy => SState { bids: b, ..s },
        Side::Sell => SState { asks: b, ..s },
    }
}

/// Strict priority order: better price, or same price and earlier arrival.
pub open spec fn key_lt(ticks: u32, side: Side, a: SOrder, b: SOrder) -> bool {
    idx(ticks, side, a.price) < idx(ticks, side, b.price)
    || (idx(ticks, side, a.price) == idx(ticks, side, b.price) && seq_of(a.id) < seq_of(b.id))
}

/// Does a resting order on `maker_side` cross a taker whose limit has priority
/// index `lim` on that side?
pub open spec fn crosses(ticks: u32, maker_side: Side, o: SOrder, lim: int) -> bool {
    idx(ticks, maker_side, o.price) <= lim
}

pub open spec fn reject(s: SState, r: RejectReason) -> (SState, Seq<Event>) {
    (s, seq![Event::Rejected { reason: r }])
}

/// Match a taker with `rem` remaining against `bk` (the maker side `ms`),
/// consuming from the front while it crosses. Fully filled makers release
/// their slot onto the free stack in the order they are consumed.
///
/// Returns (maker side after, taker remaining, fill events, free stack after).
pub open spec fn match_loop(
    ticks: u32,
    ms: Side,
    bk: Seq<SOrder>,
    lim: int,
    rem: u64,
    taker: u64,
    free: Seq<u32>,
) -> (Seq<SOrder>, u64, Seq<Event>, Seq<u32>)
    decreases bk.len(),
{
    if rem == 0 || bk.len() == 0 || !crosses(ticks, ms, bk[0], lim) {
        (bk, rem, Seq::empty(), free)
    } else {
        let m = bk[0];
        if m.qty <= rem {
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: m.qty };
            let r = match_loop(
                ticks,
                ms,
                bk.drop_first(),
                lim,
                (rem - m.qty) as u64,
                taker,
                seq![slot_of(m.id) as u32] + free,
            );
            (r.0, r.1, seq![ev] + r.2, r.3)
        } else {
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: rem };
            (bk.update(0, SOrder { qty: (m.qty - rem) as u64, ..m }), 0, seq![ev], free)
        }
    }
}

/// Total quantity on the crossing prefix of `bk`.
pub open spec fn fillable(ticks: u32, ms: Side, bk: Seq<SOrder>, lim: int) -> int
    decreases bk.len(),
{
    if bk.len() == 0 || !crosses(ticks, ms, bk[0], lim) {
        0
    } else {
        bk[0].qty + fillable(ticks, ms, bk.drop_first(), lim)
    }
}

/// Number of leading orders whose priority index is `<= i`: where a new
/// order at index `i` (with a newer sequence number than all) is inserted.
pub open spec fn ins_pos(ticks: u32, side: Side, bk: Seq<SOrder>, i: int) -> int
    decreases bk.len(),
{
    if bk.len() == 0 || idx(ticks, side, bk[0].price) > i {
        0
    } else {
        1 + ins_pos(ticks, side, bk.drop_first(), i)
    }
}

pub open spec fn would_cross(s: SState, side: Side, price: u32) -> bool {
    let ms = opp(side);
    book(s, ms).len() > 0 && crosses(s.ticks, ms, book(s, ms)[0], idx(s.ticks, ms, price))
}

pub open spec fn rests(tif: Tif) -> bool {
    tif is Gtc || tif is PostOnly
}

/// Enter an already validated order: allocate an id, match, then rest or
/// expire the remainder.
pub open spec fn submit(s: SState, side: Side, price: u32, qty: u64, tif: Tif) -> (SState, Seq<Event>) {
    let slot = s.free[0];
    let id = make_id(s.next_seq, slot);
    let ms = opp(side);
    let lim = idx(s.ticks, ms, price);
    let r = match_loop(s.ticks, ms, book(s, ms), lim, qty, id, s.free.drop_first());
    let opp2 = r.0;
    let rem = r.1;
    let fills = r.2;
    let free1 = r.3;
    let own = book(s, side);
    let rest = rem > 0 && rests(tif);
    let own2 = if rest {
        own.insert(ins_pos(s.ticks, side, own, idx(s.ticks, side, price)), SOrder { id, price, qty: rem })
    } else {
        own
    };
    let free2 = if rest { free1 } else { seq![slot] + free1 };
    let tail = if rest {
        seq![Event::Rested { id, qty: rem }]
    } else if rem > 0 {
        seq![Event::Expired { id, qty: rem }]
    } else {
        Seq::empty()
    };
    let s1 = with_book(with_book(s, ms, opp2), side, own2);
    (
        SState { free: free2, next_seq: (s.next_seq + 1) as u64, ..s1 },
        seq![Event::Accepted { id, side, price, qty }] + fills + tail,
    )
}

pub open spec fn has_id(bk: Seq<SOrder>, id: u64) -> bool {
    exists|j: int| 0 <= j < bk.len() && bk[j].id == id
}

pub open spec fn pos_of(bk: Seq<SOrder>, id: u64) -> int {
    choose|j: int| 0 <= j < bk.len() && bk[j].id == id
}

/// Where a resting order with this id lives, if anywhere.
pub open spec fn find(s: SState, id: u64) -> Option<(Side, int)> {
    if has_id(s.bids, id) {
        Some((Side::Buy, pos_of(s.bids, id)))
    } else if has_id(s.asks, id) {
        Some((Side::Sell, pos_of(s.asks, id)))
    } else {
        None
    }
}

/// Remove the resting order at `j` on `side` and free its slot.
pub open spec fn remove_at(s: SState, side: Side, j: int) -> SState {
    let o = book(s, side)[j];
    SState { free: seq![slot_of(o.id) as u32] + s.free, ..with_book(s, side, book(s, side).remove(j)) }
}

pub open spec fn valid_qty(q: u64) -> bool {
    1 <= q && q <= MAX_QTY
}

pub open spec fn step_new(s: SState, side: Side, ord_type: OrdType, tif: Tif, price: u32, qty: u64) -> (SState, Seq<Event>) {
    let px = match ord_type {
        OrdType::Limit => price,
        OrdType::Market => market_price(s.ticks, side),
    };
    let ms = opp(side);
    if ord_type is Market && !(tif is Ioc || tif is Fok) {
        reject(s, RejectReason::InvalidTif)
    } else if ord_type is Limit && price >= s.ticks {
        reject(s, RejectReason::InvalidPrice)
    } else if !valid_qty(qty) {
        reject(s, RejectReason::InvalidQty)
    } else if s.next_seq > MAX_SEQ {
        reject(s, RejectReason::SeqExhausted)
    } else if s.free.len() == 0 {
        reject(s, RejectReason::BookFull)
    } else if tif is PostOnly && would_cross(s, side, px) {
        reject(s, RejectReason::WouldCross)
    } else if tif is Fok && fillable(s.ticks, ms, book(s, ms), idx(s.ticks, ms, px)) < qty {
        reject(s, RejectReason::FokUnfillable)
    } else {
        submit(s, side, px, qty, tif)
    }
}

pub open spec fn step_cancel(s: SState, id: u64) -> (SState, Seq<Event>) {
    match find(s, id) {
        None => reject(s, RejectReason::UnknownOrder),
        Some((side, j)) => {
            let o = book(s, side)[j];
            (remove_at(s, side, j), seq![Event::Cancelled { id, qty: o.qty }])
        },
    }
}

pub open spec fn step_replace(s: SState, id: u64, price: u32, qty: u64, post_only: bool) -> (SState, Seq<Event>) {
    if price >= s.ticks {
        reject(s, RejectReason::InvalidPrice)
    } else if !valid_qty(qty) {
        reject(s, RejectReason::InvalidQty)
    } else {
        match find(s, id) {
            None => reject(s, RejectReason::UnknownOrder),
            Some((side, j)) => {
                let o = book(s, side)[j];
                if price == o.price && qty <= o.qty {
                    (
                        with_book(s, side, book(s, side).update(j, SOrder { qty, ..o })),
                        seq![Event::Reduced { id, from: o.qty, to: qty }],
                    )
                } else if s.next_seq > MAX_SEQ {
                    reject(s, RejectReason::SeqExhausted)
                } else if post_only && would_cross(s, side, price) {
                    reject(s, RejectReason::WouldCross)
                } else {
                    let s1 = remove_at(s, side, j);
                    let tif = if post_only { Tif::PostOnly } else { Tif::Gtc };
                    let r = submit(s1, side, price, qty, tif);
                    (r.0, seq![Event::Cancelled { id, qty: o.qty }] + r.1)
                }
            },
        }
    }
}

/// The engine's transition function.
pub open spec fn step(s: SState, c: Command) -> (SState, Seq<Event>) {
    match c {
        Command::New { side, ord_type, tif, price, qty } => step_new(s, side, ord_type, tif, price, qty),
        Command::Cancel { id } => step_cancel(s, id),
        Command::Replace { id, price, qty, post_only } => step_replace(s, id, price, qty, post_only),
    }
}

/// Run a command log from a state: the final state and the concatenated events.
pub open spec fn replay(s: SState, log: Seq<Command>) -> (SState, Seq<Event>)
    decreases log.len(),
{
    if log.len() == 0 {
        (s, Seq::empty())
    } else {
        let r1 = step(s, log[0]);
        let r2 = replay(r1.0, log.drop_first());
        (r2.0, r1.1 + r2.1)
    }
}

/// The initial state: empty book, all `cap` slots free in order 0, 1, ...
pub open spec fn init(ticks: u32, cap: u32) -> SState {
    SState {
        ticks,
        bids: Seq::empty(),
        asks: Seq::empty(),
        free: Seq::new(cap as nat, |i: int| i as u32),
        next_seq: 0,
    }
}

// ---------------------------------------------------------------------------
// The invariant of the reference model.

pub open spec fn sorted(ticks: u32, side: Side, bk: Seq<SOrder>) -> bool {
    forall|i: int, j: int| 0 <= i < j < bk.len() ==> #[trigger] key_lt(ticks, side, bk[i], bk[j])
}

pub open spec fn order_ok(ticks: u32, next_seq: u64, o: SOrder) -> bool {
    &&& o.price < ticks
    &&& valid_qty(o.qty)
    &&& seq_of(o.id) < next_seq
}

pub open spec fn orders_ok(ticks: u32, next_seq: u64, bk: Seq<SOrder>) -> bool {
    forall|i: int| 0 <= i < bk.len() ==> #[trigger] order_ok(ticks, next_seq, bk[i])
}

pub open spec fn ids_unique(bk: Seq<SOrder>) -> bool {
    forall|i: int, j: int| 0 <= i < bk.len() && 0 <= j < bk.len() && i != j ==> bk[i].id != bk[j].id
}

pub open spec fn ids_disjoint(a: Seq<SOrder>, b: Seq<SOrder>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i].id != b[j].id
}

pub open spec fn uncrossed(s: SState) -> bool {
    s.bids.len() > 0 && s.asks.len() > 0 ==> s.bids[0].price < s.asks[0].price
}

pub open spec fn inv(s: SState) -> bool {
    &&& 1 <= s.ticks <= MAX_TICKS
    &&& sorted(s.ticks, Side::Buy, s.bids)
    &&& sorted(s.ticks, Side::Sell, s.asks)
    &&& orders_ok(s.ticks, s.next_seq, s.bids)
    &&& orders_ok(s.ticks, s.next_seq, s.asks)
    &&& ids_unique(s.bids)
    &&& ids_unique(s.asks)
    &&& ids_disjoint(s.bids, s.asks)
    &&& forall|k: int| 0 <= k < s.free.len() ==> (#[trigger] s.free[k]) < SLOT_SPACE
    &&& uncrossed(s)
}

} // verus!
