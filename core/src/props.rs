//! Theorems about the reference model. Because the engine is proven to refine
//! `spec::step`, every theorem here is a theorem about the engine.
//!
//! Headline results (all for any state satisfying `inv`):
//! * `theorem_inv`            — every command preserves the invariant: both
//!                              sides strictly sorted by price-time priority,
//!                              ids unique, quantities in range, book never
//!                              crossed (best bid < best ask).
//! * `theorem_ledger`         — quantity is conserved: resting quantity changes
//!                              by exactly what the events report.
//! * `theorem_new_order`      — a new order fills strictly against the front
//!                              of the opposite book (price-time priority),
//!                              every fill is at the maker's price and within
//!                              the taker's limit, taker quantity is fully
//!                              accounted for, FOK is all-or-nothing and
//!                              post-only never takes liquidity.
//! * `theorem_reject_noop`    — a rejected command changes nothing.
//! * `theorem_replay_compose` — replay is compositional, so snapshot + log
//!                              suffix recovery equals full replay.

use crate::{spec::*, types::*};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Accounting helpers.

pub open spec fn qsum(bk: Seq<SOrder>) -> int
    decreases bk.len(),
{
    if bk.len() == 0 { 0 } else { bk[0].qty + qsum(bk.drop_first()) }
}

pub open spec fn total(s: SState) -> int {
    qsum(s.bids) + qsum(s.asks)
}

/// Change in resting quantity reported by one event.
pub open spec fn book_delta(e: Event) -> int {
    match e {
        Event::Rested { qty, .. } => qty as int,
        Event::Fill { qty, .. } => -(qty as int),
        Event::Cancelled { qty, .. } => -(qty as int),
        Event::Reduced { from, to, .. } => to as int - from as int,
        _ => 0,
    }
}

pub open spec fn delta_sum(evs: Seq<Event>) -> int
    decreases evs.len(),
{
    if evs.len() == 0 { 0 } else { book_delta(evs[0]) + delta_sum(evs.drop_first()) }
}

pub open spec fn fill_qty(e: Event) -> int {
    match e {
        Event::Fill { qty, .. } => qty as int,
        _ => 0,
    }
}

pub open spec fn fsum(evs: Seq<Event>) -> int
    decreases evs.len(),
{
    if evs.len() == 0 { 0 } else { fill_qty(evs[0]) + fsum(evs.drop_first()) }
}

/// Fills consume the maker book strictly from the front: the k-th fill is
/// against the k-th best resting order, at that order's price, and every fill
/// but the last takes the whole maker.
pub open spec fn fills_follow_priority(fills: Seq<Event>, bk: Seq<SOrder>, taker: u64) -> bool {
    &&& fills.len() <= bk.len()
    &&& forall|k: int| 0 <= k < fills.len() ==> {
        &&& (#[trigger] fills[k]) is Fill
        &&& fills[k]->Fill_taker == taker
        &&& fills[k]->Fill_maker == bk[k].id
        &&& fills[k]->Fill_price == bk[k].price
        &&& 1 <= fills[k]->Fill_qty <= bk[k].qty
        &&& (k + 1 < fills.len() ==> fills[k]->Fill_qty == bk[k].qty)
    }
}

/// Every filled maker was within the taker's limit.
pub open spec fn fills_within_limit(ticks: u32, ms: Side, bk: Seq<SOrder>, n: int, lim: int) -> bool {
    forall|k: int| 0 <= k < n ==> #[trigger] crosses(ticks, ms, bk[k], lim)
}

/// The maker book after matching `n` makers: either exactly the untouched
/// suffix, or the suffix with its first order partially filled.
pub open spec fn book_after_shape(bk: Seq<SOrder>, n: int, after: Seq<SOrder>) -> bool {
    ||| after =~= bk.skip(n)
    ||| (1 <= n && after.len() == bk.len() - n + 1 && after.len() >= 1
        && after.skip(1) =~= bk.skip(n)
        && after[0].id == bk[n - 1].id && after[0].price == bk[n - 1].price
        && 1 <= after[0].qty < bk[n - 1].qty)
}

// ---------------------------------------------------------------------------
// Generic sequence lemmas.

pub proof fn lemma_qsum_nonneg(bk: Seq<SOrder>)
    ensures qsum(bk) >= 0,
    decreases bk.len(),
{
    if bk.len() > 0 { lemma_qsum_nonneg(bk.drop_first()); }
}

pub proof fn lemma_qsum_add(a: Seq<SOrder>, b: Seq<SOrder>)
    ensures qsum(a + b) == qsum(a) + qsum(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_qsum_add(a.drop_first(), b);
    }
}

pub proof fn lemma_qsum_split(bk: Seq<SOrder>, j: int)
    requires 0 <= j < bk.len(),
    ensures qsum(bk) == qsum(bk.take(j)) + bk[j].qty + qsum(bk.skip(j + 1)),
{
    reveal_with_fuel(qsum, 2);
    assert(bk =~= bk.take(j) + (seq![bk[j]] + bk.skip(j + 1)));
    lemma_qsum_add(bk.take(j), seq![bk[j]] + bk.skip(j + 1));
    lemma_qsum_add(seq![bk[j]], bk.skip(j + 1));
    assert(seq![bk[j]].drop_first() =~= Seq::<SOrder>::empty());
}

pub proof fn lemma_qsum_remove(bk: Seq<SOrder>, j: int)
    requires 0 <= j < bk.len(),
    ensures qsum(bk.remove(j)) == qsum(bk) - bk[j].qty,
{
    lemma_qsum_split(bk, j);
    assert(bk.remove(j) =~= bk.take(j) + bk.skip(j + 1));
    lemma_qsum_add(bk.take(j), bk.skip(j + 1));
}

pub proof fn lemma_qsum_insert(bk: Seq<SOrder>, j: int, o: SOrder)
    requires 0 <= j <= bk.len(),
    ensures qsum(bk.insert(j, o)) == qsum(bk) + o.qty,
{
    let b2 = bk.insert(j, o);
    assert(b2[j] == o);
    lemma_qsum_split(b2, j);
    assert(b2.take(j) =~= bk.take(j));
    assert(b2.skip(j + 1) =~= bk.skip(j));
    assert(bk =~= bk.take(j) + bk.skip(j));
    lemma_qsum_add(bk.take(j), bk.skip(j));
}

pub proof fn lemma_qsum_update(bk: Seq<SOrder>, j: int, o: SOrder)
    requires 0 <= j < bk.len(),
    ensures qsum(bk.update(j, o)) == qsum(bk) - bk[j].qty + o.qty,
{
    let b2 = bk.update(j, o);
    lemma_qsum_split(bk, j);
    lemma_qsum_split(b2, j);
    assert(b2.take(j) =~= bk.take(j));
    assert(b2.skip(j + 1) =~= bk.skip(j + 1));
}

pub proof fn lemma_fsum_add(a: Seq<Event>, b: Seq<Event>)
    ensures fsum(a + b) == fsum(a) + fsum(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_fsum_add(a.drop_first(), b);
    }
}

pub proof fn lemma_delta_sum_add(a: Seq<Event>, b: Seq<Event>)
    ensures delta_sum(a + b) == delta_sum(a) + delta_sum(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_delta_sum_add(a.drop_first(), b);
    }
}

pub proof fn lemma_delta_sum_one(e: Event)
    ensures delta_sum(seq![e]) == book_delta(e),
{
    reveal_with_fuel(delta_sum, 2);
    assert(seq![e].drop_first() =~= Seq::<Event>::empty());
}

pub proof fn lemma_fsum_one(e: Event)
    ensures fsum(seq![e]) == fill_qty(e),
{
    reveal_with_fuel(fsum, 2);
    assert(seq![e].drop_first() =~= Seq::<Event>::empty());
}

/// For a sequence of fills, the book delta is minus the filled quantity.
pub proof fn lemma_delta_of_fills(fills: Seq<Event>)
    requires forall|k: int| 0 <= k < fills.len() ==> (#[trigger] fills[k]) is Fill,
    ensures delta_sum(fills) == -fsum(fills),
    decreases fills.len(),
{
    if fills.len() > 0 {
        lemma_delta_of_fills(fills.drop_first());
    }
}

// ---------------------------------------------------------------------------
// Book-shape preservation lemmas.

pub proof fn lemma_sorted_skip(ticks: u32, side: Side, bk: Seq<SOrder>, n: int)
    requires sorted(ticks, side, bk), 0 <= n <= bk.len(),
    ensures sorted(ticks, side, bk.skip(n)),
{
    assert forall|i: int, j: int| 0 <= i < j < bk.skip(n).len()
        implies #[trigger] key_lt(ticks, side, bk.skip(n)[i], bk.skip(n)[j]) by {
        assert(key_lt(ticks, side, bk[i + n], bk[j + n]));
    }
}

pub proof fn lemma_sorted_remove(ticks: u32, side: Side, bk: Seq<SOrder>, r: int)
    requires sorted(ticks, side, bk), 0 <= r < bk.len(),
    ensures sorted(ticks, side, bk.remove(r)),
{
    let b2 = bk.remove(r);
    assert forall|i: int, j: int| 0 <= i < j < b2.len()
        implies #[trigger] key_lt(ticks, side, b2[i], b2[j]) by {
        let i0 = if i < r { i } else { i + 1 };
        let j0 = if j < r { j } else { j + 1 };
        assert(b2[i] == bk[i0] && b2[j] == bk[j0]);
        assert(key_lt(ticks, side, bk[i0], bk[j0]));
    }
}

/// Changing only the quantity of an order keeps the book sorted.
pub proof fn lemma_sorted_update_qty(ticks: u32, side: Side, bk: Seq<SOrder>, j: int, q: u64)
    requires sorted(ticks, side, bk), 0 <= j < bk.len(),
    ensures sorted(ticks, side, bk.update(j, SOrder { qty: q, ..bk[j] })),
{
    let b2 = bk.update(j, SOrder { qty: q, ..bk[j] });
    assert forall|a: int, b: int| 0 <= a < b < b2.len()
        implies #[trigger] key_lt(ticks, side, b2[a], b2[b]) by {
        assert(key_lt(ticks, side, bk[a], bk[b]));
    }
}

/// Sortedness implies the priority index is non-decreasing.
pub proof fn lemma_sorted_idx_mono(ticks: u32, side: Side, bk: Seq<SOrder>, i: int, j: int)
    requires sorted(ticks, side, bk), 0 <= i <= j < bk.len(),
    ensures idx(ticks, side, bk[i].price) <= idx(ticks, side, bk[j].price),
{
    if i < j {
        assert(key_lt(ticks, side, bk[i], bk[j]));
    }
}

pub proof fn lemma_ins_pos(ticks: u32, side: Side, bk: Seq<SOrder>, i: int)
    requires sorted(ticks, side, bk),
    ensures
        0 <= ins_pos(ticks, side, bk, i) <= bk.len(),
        forall|k: int| 0 <= k < ins_pos(ticks, side, bk, i) ==> idx(ticks, side, (#[trigger] bk[k]).price) <= i,
        forall|k: int| ins_pos(ticks, side, bk, i) <= k < bk.len() ==> idx(ticks, side, (#[trigger] bk[k]).price) > i,
    decreases bk.len(),
{
    if bk.len() == 0 {
    } else if idx(ticks, side, bk[0].price) > i {
        assert forall|k: int| 0 <= k < bk.len() implies idx(ticks, side, (#[trigger] bk[k]).price) > i by {
            lemma_sorted_idx_mono(ticks, side, bk, 0, k);
        }
    } else {
        let t = bk.drop_first();
        lemma_sorted_skip(ticks, side, bk, 1);
        assert(t =~= bk.skip(1));
        lemma_ins_pos(ticks, side, t, i);
        assert forall|k: int| 0 <= k < ins_pos(ticks, side, bk, i)
            implies idx(ticks, side, (#[trigger] bk[k]).price) <= i by {
            if k > 0 { assert(bk[k] == t[k - 1]); }
        }
        assert forall|k: int| ins_pos(ticks, side, bk, i) <= k < bk.len()
            implies idx(ticks, side, (#[trigger] bk[k]).price) > i by {
            assert(bk[k] == t[k - 1]);
        }
    }
}

/// Inserting a strictly newer order at its insertion position keeps the book
/// sorted.
pub proof fn lemma_sorted_insert(ticks: u32, side: Side, bk: Seq<SOrder>, o: SOrder)
    requires
        sorted(ticks, side, bk),
        forall|k: int| 0 <= k < bk.len() ==> seq_of((#[trigger] bk[k]).id) < seq_of(o.id),
    ensures
        sorted(ticks, side, bk.insert(ins_pos(ticks, side, bk, idx(ticks, side, o.price)), o)),
{
    let i = idx(ticks, side, o.price);
    let p = ins_pos(ticks, side, bk, i);
    lemma_ins_pos(ticks, side, bk, i);
    let b2 = bk.insert(p, o);
    assert forall|a: int, b: int| 0 <= a < b < b2.len()
        implies #[trigger] key_lt(ticks, side, b2[a], b2[b]) by {
        if b < p {
            assert(key_lt(ticks, side, bk[a], bk[b]));
        } else if b == p {
            assert(b2[a] == bk[a]);
        } else if a == p {
            assert(b2[b] == bk[b - 1]);
        } else if a < p {
            assert(key_lt(ticks, side, bk[a], bk[b - 1]));
        } else {
            assert(key_lt(ticks, side, bk[a - 1], bk[b - 1]));
        }
    }
}

// ---------------------------------------------------------------------------
// The matching loop.

pub proof fn lemma_match_loop(
    ticks: u32,
    ms: Side,
    bk: Seq<SOrder>,
    lim: int,
    rem: u64,
    taker: u64,
    free: Seq<u32>,
)
    requires
        forall|k: int| 0 <= k < bk.len() ==> 1 <= (#[trigger] bk[k]).qty,
        forall|k: int| 0 <= k < free.len() ==> (#[trigger] free[k]) < SLOT_SPACE,
    ensures ({
        let r = match_loop(ticks, ms, bk, lim, rem, taker, free);
        let n = r.2.len() as int;
        &&& r.1 <= rem
        &&& fsum(r.2) == rem - r.1
        &&& qsum(r.0) == qsum(bk) - (rem - r.1)
        &&& fills_follow_priority(r.2, bk, taker)
        &&& fills_within_limit(ticks, ms, bk, n, lim)
        &&& book_after_shape(bk, n, r.0)
        &&& (r.1 == 0 || r.0.len() == 0 || !crosses(ticks, ms, r.0[0], lim))
        &&& (r.1 > 0 ==> r.0 =~= bk.skip(n))
        &&& forall|k: int| 0 <= k < r.3.len() ==> (#[trigger] r.3[k]) < SLOT_SPACE
    }),
    decreases bk.len(),
{
    let r = match_loop(ticks, ms, bk, lim, rem, taker, free);
    if rem == 0 || bk.len() == 0 || !crosses(ticks, ms, bk[0], lim) {
        assert(bk.skip(0) =~= bk);
    } else {
        let m = bk[0];
        if m.qty <= rem {
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: m.qty };
            let t = bk.drop_first();
            let f2 = seq![slot_of(m.id) as u32] + free;
            assert forall|k: int| 0 <= k < f2.len() implies (#[trigger] f2[k]) < SLOT_SPACE by {
                if k > 0 { assert(f2[k] == free[k - 1]); }
            }
            let r2 = match_loop(ticks, ms, t, lim, (rem - m.qty) as u64, taker, f2);
            lemma_match_loop(ticks, ms, t, lim, (rem - m.qty) as u64, taker, f2);
            assert(r == (r2.0, r2.1, seq![ev] + r2.2, r2.3));
            lemma_fsum_add(seq![ev], r2.2);
            lemma_fsum_one(ev);
            let n2 = r2.2.len() as int;
            assert forall|k: int| 0 <= k < r.2.len() implies {
                &&& (#[trigger] r.2[k]) is Fill
                &&& r.2[k]->Fill_taker == taker
                &&& r.2[k]->Fill_maker == bk[k].id
                &&& r.2[k]->Fill_price == bk[k].price
                &&& 1 <= r.2[k]->Fill_qty <= bk[k].qty
                &&& (k + 1 < r.2.len() ==> r.2[k]->Fill_qty == bk[k].qty)
            } by {
                if k > 0 {
                    assert(r.2[k] == r2.2[k - 1]);
                    assert(bk[k] == t[k - 1]);
                }
            }
            assert forall|k: int| 0 <= k < n2 + 1 implies #[trigger] crosses(ticks, ms, bk[k], lim) by {
                if k > 0 {
                    assert(bk[k] == t[k - 1]);
                    assert(crosses(ticks, ms, t[k - 1], lim));
                }
            }
            assert(t.skip(n2) =~= bk.skip(n2 + 1));
            if n2 >= 1 {
                assert(t.skip(n2 - 1) =~= bk.skip(n2));
                assert(t[n2 - 1] == bk[n2]);
            }
        } else {
            let b2 = bk.update(0, SOrder { qty: (m.qty - rem) as u64, ..m });
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: rem };
            assert(r == (b2, 0u64, seq![ev], free));
            lemma_fsum_one(ev);
            lemma_qsum_update(bk, 0, SOrder { qty: (m.qty - rem) as u64, ..m });
            assert(b2.skip(1) =~= bk.skip(1));
            assert(bk.skip(0) =~= bk);
        }
    }
}

/// The free stack after matching: every slot pushed is a slot of a filled maker.
pub proof fn lemma_fillable_ge(
    ticks: u32,
    ms: Side,
    bk: Seq<SOrder>,
    lim: int,
    rem: u64,
    taker: u64,
    free: Seq<u32>,
)
    requires
        forall|k: int| 0 <= k < bk.len() ==> 1 <= (#[trigger] bk[k]).qty,
        forall|k: int| 0 <= k < free.len() ==> (#[trigger] free[k]) < SLOT_SPACE,
        fillable(ticks, ms, bk, lim) >= rem,
    ensures
        match_loop(ticks, ms, bk, lim, rem, taker, free).1 == 0,
    decreases bk.len(),
{
    if rem == 0 || bk.len() == 0 || !crosses(ticks, ms, bk[0], lim) {
    } else {
        let m = bk[0];
        if m.qty <= rem {
            let f2 = seq![slot_of(m.id) as u32] + free;
            assert forall|k: int| 0 <= k < f2.len() implies (#[trigger] f2[k]) < SLOT_SPACE by {
                if k > 0 { assert(f2[k] == free[k - 1]); }
            }
            lemma_fillable_ge(ticks, ms, bk.drop_first(), lim, (rem - m.qty) as u64, taker, f2);
        }
    }
}

// ---------------------------------------------------------------------------
// Preservation of the invariant.

pub proof fn lemma_ok_mono(ticks: u32, n1: u64, n2: u64, bk: Seq<SOrder>)
    requires orders_ok(ticks, n1, bk), n1 <= n2,
    ensures orders_ok(ticks, n2, bk),
{
    assert forall|i: int| 0 <= i < bk.len() implies #[trigger] order_ok(ticks, n2, bk[i]) by {
        assert(order_ok(ticks, n1, bk[i]));
    }
}

/// Facts about the maker book after matching, from its shape.
pub proof fn lemma_after_shape(ticks: u32, ms: Side, ns: u64, bk: Seq<SOrder>, n: int, after: Seq<SOrder>)
    requires
        book_after_shape(bk, n, after),
        0 <= n <= bk.len(),
        sorted(ticks, ms, bk),
        orders_ok(ticks, ns, bk),
        ids_unique(bk),
    ensures
        sorted(ticks, ms, after),
        orders_ok(ticks, ns, after),
        ids_unique(after),
        forall|i: int| 0 <= i < after.len() ==> exists|k: int| 0 <= k < bk.len() && #[trigger] after[i].id == bk[k].id && after[i].price == bk[k].price,
        after.len() > 0 && bk.len() > 0 ==> idx(ticks, ms, bk[0].price) <= idx(ticks, ms, after[0].price),
{
    if after =~= bk.skip(n) {
        lemma_sorted_skip(ticks, ms, bk, n);
        assert forall|i: int| 0 <= i < after.len() implies exists|k: int| 0 <= k < bk.len() && #[trigger] after[i].id == bk[k].id && after[i].price == bk[k].price by {
            assert(after[i] == bk[i + n]);
        }
        if after.len() > 0 && bk.len() > 0 {
            lemma_sorted_idx_mono(ticks, ms, bk, 0, n);
        }
    } else {
        let a0 = after[0];
        assert(after =~= bk.skip(n - 1).update(0, SOrder { qty: a0.qty, ..bk[n - 1] })) by {
            assert forall|i: int| 1 <= i < after.len() implies after[i] == bk.skip(n - 1)[i] by {
                assert(after[i] == after.skip(1)[i - 1]);
            }
        }
        lemma_sorted_skip(ticks, ms, bk, n - 1);
        lemma_sorted_update_qty(ticks, ms, bk.skip(n - 1), 0, a0.qty);
        assert forall|i: int| 0 <= i < after.len() implies exists|k: int| 0 <= k < bk.len() && #[trigger] after[i].id == bk[k].id && after[i].price == bk[k].price by {
            if i == 0 { assert(after[i].id == bk[n - 1].id); } else { assert(after[i] == bk[i + n - 1]); }
        }
        lemma_sorted_idx_mono(ticks, ms, bk, 0, n - 1);
    }
    assert forall|i: int| 0 <= i < after.len() implies #[trigger] order_ok(ticks, ns, after[i]) by {
        if after =~= bk.skip(n) {
            assert(order_ok(ticks, ns, bk[i + n]));
        } else if i == 0 {
            assert(order_ok(ticks, ns, bk[n - 1]));
        } else {
            assert(after[i] == after.skip(1)[i - 1]);
            assert(order_ok(ticks, ns, bk[i + n - 1]));
        }
    }
    assert forall|i: int, j: int| 0 <= i < after.len() && 0 <= j < after.len() && i != j
        implies after[i].id != after[j].id by {
        let ii = if after =~= bk.skip(n) { i + n } else { i + n - 1 };
        let jj = if after =~= bk.skip(n) { j + n } else { j + n - 1 };
        if !(after =~= bk.skip(n)) {
            if i > 0 { assert(after[i] == after.skip(1)[i - 1]); }
            if j > 0 { assert(after[j] == after.skip(1)[j - 1]); }
        }
        assert(after[i].id == bk[ii].id);
        assert(after[j].id == bk[jj].id);
    }
}

pub open spec fn submit_ok(s: SState, side: Side, price: u32, qty: u64, tif: Tif) -> bool {
    &&& s.free.len() > 0
    &&& s.next_seq <= MAX_SEQ
    &&& price < s.ticks
    &&& valid_qty(qty)
    &&& (tif is PostOnly ==> !would_cross(s, side, price))
}

pub open spec fn submit_fills(s: SState, side: Side, price: u32, qty: u64) -> Seq<Event> {
    let ms = opp(side);
    match_loop(s.ticks, ms, book(s, ms), idx(s.ticks, ms, price), qty, make_id(s.next_seq, s.free[0]), s.free.drop_first()).2
}

pub open spec fn tail_qty(evs: Seq<Event>) -> int
    decreases evs.len(),
{
    if evs.len() == 0 {
        0
    } else {
        (match evs[0] {
            Event::Rested { qty, .. } => qty as int,
            Event::Expired { qty, .. } => qty as int,
            _ => 0,
        }) + tail_qty(evs.drop_first())
    }
}

pub proof fn lemma_inv_book(s: SState, side: Side)
    requires inv(s),
    ensures
        sorted(s.ticks, side, book(s, side)),
        orders_ok(s.ticks, s.next_seq, book(s, side)),
        ids_unique(book(s, side)),
        forall|k: int| 0 <= k < book(s, side).len() ==> 1 <= (#[trigger] book(s, side)[k]).qty,
{
    assert forall|k: int| 0 <= k < book(s, side).len() implies 1 <= (#[trigger] book(s, side)[k]).qty by {
        assert(order_ok(s.ticks, s.next_seq, book(s, side)[k]));
    }
}

pub proof fn lemma_make_id(n: u64, slot: u32)
    requires n <= MAX_SEQ, slot < SLOT_SPACE,
    ensures
        seq_of(make_id(n, slot)) == n,
        slot_of(make_id(n, slot)) == slot,
        make_id(n, slot) as int == n * SLOT_SPACE + slot,
{
    let v: int = n as int * 16777216 + slot as int;
    assert(v <= 18446744073709551615) by (nonlinear_arith)
        requires n <= 1099511627775, slot < 16777216, v == n as int * 16777216 + slot as int;
    assert(v >= 0) by (nonlinear_arith) requires v == n as int * 16777216 + slot as int, n >= 0, slot >= 0;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v, 16777216, n as int, slot as int);
}

/// Everything about `submit`.
pub proof fn lemma_submit(s: SState, side: Side, price: u32, qty: u64, tif: Tif)
    requires inv(s), submit_ok(s, side, price, qty, tif),
    ensures ({
        let r = submit(s, side, price, qty, tif);
        let ms = opp(side);
        let id = make_id(s.next_seq, s.free[0]);
        let fills = submit_fills(s, side, price, qty);
        let tail = r.1.skip(1 + fills.len() as int);
        &&& inv(r.0)
        &&& r.1 =~= seq![Event::Accepted { id, side, price, qty }] + fills + tail
        &&& fills_follow_priority(fills, book(s, ms), id)
        &&& fills_within_limit(s.ticks, ms, book(s, ms), fills.len() as int, idx(s.ticks, ms, price))
        &&& fsum(fills) + tail_qty(tail) == qty
        &&& total(r.0) == total(s) + delta_sum(r.1)
        &&& (tif is PostOnly ==> fills.len() == 0)
    }),
{
    let ticks = s.ticks;
    let slot = s.free[0];
    let id = make_id(s.next_seq, slot);
    let ms = opp(side);
    let lim = idx(ticks, ms, price);
    let bk = book(s, ms);
    let own = book(s, side);
    let free0 = s.free.drop_first();
    lemma_inv_book(s, ms);
    lemma_inv_book(s, side);
    assert(slot < SLOT_SPACE);
    lemma_make_id(s.next_seq, slot);
    assert forall|k: int| 0 <= k < free0.len() implies (#[trigger] free0[k]) < SLOT_SPACE by {
        assert(free0[k] == s.free[k + 1]);
    }
    let m = match_loop(ticks, ms, bk, lim, qty, id, free0);
    lemma_match_loop(ticks, ms, bk, lim, qty, id, free0);
    let n = m.2.len() as int;
    let opp2 = m.0;
    let rem = m.1;
    let fills = m.2;
    lemma_after_shape(ticks, ms, s.next_seq, bk, n, opp2);
    let rest = rem > 0 && rests(tif);
    let o = SOrder { id, price, qty: rem };
    let p = ins_pos(ticks, side, own, idx(ticks, side, price));
    let own2 = if rest { own.insert(p, o) } else { own };
    let r = submit(s, side, price, qty, tif);
    let ns = (s.next_seq + 1) as u64;
    let tail = if rest {
        seq![Event::Rested { id, qty: rem }]
    } else if rem > 0 {
        seq![Event::Expired { id, qty: rem }]
    } else {
        Seq::<Event>::empty()
    };
    assert(r.1 =~= seq![Event::Accepted { id, side, price, qty }] + fills + tail);
    assert(r.1.skip(1 + fills.len() as int) =~= tail);

    // own side after
    lemma_ok_mono(ticks, s.next_seq, ns, own);
    lemma_ok_mono(ticks, s.next_seq, ns, opp2);
    if rest {
        assert forall|k: int| 0 <= k < own.len() implies seq_of((#[trigger] own[k]).id) < seq_of(o.id) by {
            assert(order_ok(ticks, s.next_seq, own[k]));
        }
        lemma_sorted_insert(ticks, side, own, o);
        lemma_ins_pos(ticks, side, own, idx(ticks, side, price));
        assert forall|i: int| 0 <= i < own2.len() implies #[trigger] order_ok(ticks, ns, own2[i]) by {
            if i < p { assert(order_ok(ticks, ns, own[i])); }
            else if i > p { assert(own2[i] == own[i - 1]); assert(order_ok(ticks, ns, own[i - 1])); }
        }
        assert forall|i: int, j: int| 0 <= i < own2.len() && 0 <= j < own2.len() && i != j
            implies own2[i].id != own2[j].id by {
            let ii = if i < p { i } else { i - 1 };
            let jj = if j < p { j } else { j - 1 };
            if i != p { assert(order_ok(ticks, s.next_seq, own[ii])); }
            if j != p { assert(order_ok(ticks, s.next_seq, own[jj])); }
        }
        lemma_qsum_insert(own, p, o);
    }
    // ids across sides
    assert forall|i: int, j: int| 0 <= i < own2.len() && 0 <= j < opp2.len()
        implies own2[i].id != opp2[j].id by {
        let k = choose|k: int| 0 <= k < bk.len() && opp2[j].id == bk[k].id && opp2[j].price == bk[k].price;
        assert(order_ok(ticks, s.next_seq, bk[k]));
        if rest && i == p {
        } else {
            let ii = if rest && i > p { i - 1 } else { i };
            assert(own2[i] == own[ii]);
            if side is Buy {
                assert(s.bids[ii].id != s.asks[k].id);
            } else {
                assert(s.bids[k].id != s.asks[ii].id);
            }
        }
    }
    // uncrossed
    if own2.len() > 0 && opp2.len() > 0 {
        if rest {
            // taker rested: what is left on the opposite side does not cross it
            assert(!crosses(ticks, ms, opp2[0], lim));
            if p > 0 {
                lemma_ins_pos(ticks, side, own, idx(ticks, side, price));
                assert(own2[0] == own[0]);
                assert(idx(ticks, side, own[0].price) <= idx(ticks, side, price));
            }
        } else {
            assert(own2 =~= own);
            assert(bk.len() > 0);
        }
    }
    // free stack
    let free2 = if rest { m.3 } else { seq![slot] + m.3 };
    assert forall|k: int| 0 <= k < free2.len() implies (#[trigger] free2[k]) < SLOT_SPACE by {
        if !rest && k > 0 { assert(free2[k] == m.3[k - 1]); }
    }
    // ledger
    assert forall|k: int| 0 <= k < fills.len() implies (#[trigger] fills[k]) is Fill by {}
    lemma_delta_of_fills(fills);
    lemma_delta_sum_add(seq![Event::Accepted { id, side, price, qty }], fills);
    lemma_delta_sum_add(seq![Event::Accepted { id, side, price, qty }] + fills, tail);
    lemma_delta_sum_one(Event::Accepted { id, side, price, qty });
    if rest {
        lemma_delta_sum_one(Event::Rested { id, qty: rem });
        assert(tail.drop_first() =~= Seq::<Event>::empty());
    } else if rem > 0 {
        lemma_delta_sum_one(Event::Expired { id, qty: rem });
        assert(tail.drop_first() =~= Seq::<Event>::empty());
    }
    assert(tail_qty(tail) == rem) by {
        if tail.len() > 0 { assert(tail.drop_first() =~= Seq::<Event>::empty()); }
    }
    // post-only never takes
    if tif is PostOnly {
        if bk.len() > 0 {
            assert(!crosses(ticks, ms, bk[0], lim));
        }
    }
    assert(r.0.bids == (if side is Buy { own2 } else { opp2 }));
    assert(r.0.asks == (if side is Buy { opp2 } else { own2 }));
}

pub proof fn lemma_find(s: SState, id: u64)
    requires inv(s),
    ensures
        find(s, id) matches Some((side, j)) ==> 0 <= j < book(s, side).len() && book(s, side)[j].id == id,
        find(s, id) is None ==> !has_id(s.bids, id) && !has_id(s.asks, id),
{
}

pub proof fn lemma_remove_at(s: SState, side: Side, j: int)
    requires inv(s), 0 <= j < book(s, side).len(),
    ensures
        inv(remove_at(s, side, j)),
        total(remove_at(s, side, j)) == total(s) - book(s, side)[j].qty,
{
    let bk = book(s, side);
    let b2 = bk.remove(j);
    let s2 = remove_at(s, side, j);
    lemma_inv_book(s, side);
    lemma_sorted_remove(s.ticks, side, bk, j);
    lemma_qsum_remove(bk, j);
    assert forall|i: int| 0 <= i < b2.len() implies #[trigger] order_ok(s.ticks, s.next_seq, b2[i]) by {
        if i < j { assert(b2[i] == bk[i]); } else { assert(b2[i] == bk[i + 1]); }
    }
    assert forall|a: int, b: int| 0 <= a < b2.len() && 0 <= b < b2.len() && a != b implies b2[a].id != b2[b].id by {
        let aa = if a < j { a } else { a + 1 };
        let bb = if b < j { b } else { b + 1 };
        assert(b2[a] == bk[aa] && b2[b] == bk[bb]);
    }
    let other = book(s, opp(side));
    assert forall|a: int, b: int| 0 <= a < b2.len() && 0 <= b < other.len() implies b2[a].id != other[b].id by {
        let aa = if a < j { a } else { a + 1 };
        assert(b2[a] == bk[aa]);
        if side is Buy { assert(s.bids[aa].id != s.asks[b].id); } else { assert(s.bids[b].id != s.asks[aa].id); }
    }
    let o = bk[j];
    assert(order_ok(s.ticks, s.next_seq, o));
    assert forall|k: int| 0 <= k < s2.free.len() implies (#[trigger] s2.free[k]) < SLOT_SPACE by {
        if k > 0 { assert(s2.free[k] == s.free[k - 1]); }
    }
    if b2.len() > 0 && other.len() > 0 {
        // the new best on `side` is no better than the old best
        let k0 = if j == 0 { 1int } else { 0int };
        assert(b2[0] == bk[k0]);
        lemma_sorted_idx_mono(s.ticks, side, bk, 0, k0);
    }
}

pub proof fn theorem_cancel(s: SState, id: u64)
    requires inv(s),
    ensures
        inv(step_cancel(s, id).0),
        total(step_cancel(s, id).0) == total(s) + delta_sum(step_cancel(s, id).1),
{
    lemma_find(s, id);
    match find(s, id) {
        None => {
            lemma_delta_sum_one(Event::Rejected { reason: RejectReason::UnknownOrder });
        },
        Some((side, j)) => {
            let o = book(s, side)[j];
            lemma_remove_at(s, side, j);
            lemma_delta_sum_one(Event::Cancelled { id, qty: o.qty });
        },
    }
}

pub proof fn theorem_replace(s: SState, id: u64, price: u32, qty: u64, post_only: bool)
    requires inv(s),
    ensures
        inv(step_replace(s, id, price, qty, post_only).0),
        total(step_replace(s, id, price, qty, post_only).0) == total(s) + delta_sum(step_replace(s, id, price, qty, post_only).1),
{
    let r = step_replace(s, id, price, qty, post_only);
    lemma_find(s, id);
    if price >= s.ticks || !valid_qty(qty) || find(s, id) is None {
        lemma_delta_sum_one(r.1[0]);
        assert(r.1 =~= seq![r.1[0]]);
    } else {
        let (side, j) = find(s, id).unwrap();
        let bk = book(s, side);
        let o = bk[j];
        lemma_inv_book(s, side);
        if price == o.price && qty <= o.qty {
            let b2 = bk.update(j, SOrder { qty, ..o });
            lemma_sorted_update_qty(s.ticks, side, bk, j, qty);
            lemma_qsum_update(bk, j, SOrder { qty, ..o });
            lemma_delta_sum_one(Event::Reduced { id, from: o.qty, to: qty });
            assert forall|i: int| 0 <= i < b2.len() implies #[trigger] order_ok(s.ticks, s.next_seq, b2[i]) by {
                assert(order_ok(s.ticks, s.next_seq, bk[i]));
            }
            assert forall|a: int, b: int| 0 <= a < b2.len() && 0 <= b < b2.len() && a != b implies b2[a].id != b2[b].id by {
                assert(b2[a].id == bk[a].id && b2[b].id == bk[b].id);
            }
            let other = book(s, opp(side));
            assert forall|a: int, b: int| 0 <= a < b2.len() && 0 <= b < other.len() implies b2[a].id != other[b].id by {
                assert(b2[a].id == bk[a].id);
                if side is Buy { assert(s.bids[a].id != s.asks[b].id); } else { assert(s.bids[b].id != s.asks[a].id); }
            }
            assert(b2[0].price == bk[0].price);
        } else if s.next_seq > MAX_SEQ || (post_only && would_cross(s, side, price)) {
            lemma_delta_sum_one(r.1[0]);
            assert(r.1 =~= seq![r.1[0]]);
        } else {
            let s1 = remove_at(s, side, j);
            lemma_remove_at(s, side, j);
            let tif = if post_only { Tif::PostOnly } else { Tif::Gtc };
            // removing an order on `side` does not change the opposite book
            assert(book(s1, opp(side)) == book(s, opp(side)));
            assert(would_cross(s1, side, price) == would_cross(s, side, price));
            lemma_submit(s1, side, price, qty, tif);
            let r1 = submit(s1, side, price, qty, tif);
            lemma_delta_sum_add(seq![Event::Cancelled { id, qty: o.qty }], r1.1);
            lemma_delta_sum_one(Event::Cancelled { id, qty: o.qty });
        }
    }
}

pub proof fn theorem_new(s: SState, side: Side, ord_type: OrdType, tif: Tif, price: u32, qty: u64)
    requires inv(s),
    ensures
        inv(step_new(s, side, ord_type, tif, price, qty).0),
        total(step_new(s, side, ord_type, tif, price, qty).0) == total(s) + delta_sum(step_new(s, side, ord_type, tif, price, qty).1),
{
    let r = step_new(s, side, ord_type, tif, price, qty);
    let px = match ord_type { OrdType::Limit => price, OrdType::Market => market_price(s.ticks, side) };
    let ms = opp(side);
    if r.1[0] is Rejected {
        lemma_delta_sum_one(r.1[0]);
        assert(r.1 =~= seq![r.1[0]]);
    } else {
        lemma_submit(s, side, px, qty, tif);
    }
}

// ---------------------------------------------------------------------------
// Headline theorems.

/// Every command preserves the invariant (sorted price-time priority, unique
/// ids, valid quantities, an uncrossed book).
pub proof fn theorem_inv(s: SState, c: Command)
    requires inv(s),
    ensures inv(step(s, c).0),
{
    theorem_ledger(s, c);
}

/// Quantity conservation: resting quantity changes by exactly the sum of the
/// event deltas (+rested, -filled, -cancelled, +/- reduced).
pub proof fn theorem_ledger(s: SState, c: Command)
    requires inv(s),
    ensures
        inv(step(s, c).0),
        total(step(s, c).0) == total(s) + delta_sum(step(s, c).1),
{
    match c {
        Command::New { side, ord_type, tif, price, qty } => theorem_new(s, side, ord_type, tif, price, qty),
        Command::Cancel { id } => theorem_cancel(s, id),
        Command::Replace { id, price, qty, post_only } => theorem_replace(s, id, price, qty, post_only),
    }
}

/// A rejected command has no effect on the state and emits only the rejection.
pub proof fn theorem_reject_noop(s: SState, c: Command)
    requires step(s, c).1.len() > 0 && step(s, c).1[0] is Rejected,
    ensures step(s, c).0 == s, step(s, c).1.len() == 1,
{
}

/// A new order that is accepted:
/// * gets a fresh id and an `Accepted` event first;
/// * fills strictly against the front of the opposite book in priority order,
///   always at the resting order's price, and only against orders within its
///   limit;
/// * accounts for its whole quantity as fills + rested/expired remainder;
/// * if FOK, is filled completely; if post-only, takes no liquidity.
pub proof fn theorem_new_order(s: SState, side: Side, ord_type: OrdType, tif: Tif, price: u32, qty: u64)
    requires inv(s),
    ensures ({
        let r = step_new(s, side, ord_type, tif, price, qty);
        let px = match ord_type { OrdType::Limit => price, OrdType::Market => market_price(s.ticks, side) };
        let ms = opp(side);
        let id = make_id(s.next_seq, s.free[0]);
        let fills = submit_fills(s, side, px, qty);
        let tail = r.1.skip(1 + fills.len() as int);
        !(r.1[0] is Rejected) ==> {
            &&& r.1 =~= seq![Event::Accepted { id, side, price: px, qty }] + fills + tail
            &&& fills_follow_priority(fills, book(s, ms), id)
            &&& fills_within_limit(s.ticks, ms, book(s, ms), fills.len() as int, idx(s.ticks, ms, px))
            &&& fsum(fills) + tail_qty(tail) == qty
            &&& (tif is Fok ==> fsum(fills) == qty)
            &&& (tif is PostOnly ==> fills.len() == 0)
            &&& seq_of(id) == s.next_seq
        }
    }),
{
    let r = step_new(s, side, ord_type, tif, price, qty);
    let px = match ord_type { OrdType::Limit => price, OrdType::Market => market_price(s.ticks, side) };
    let ms = opp(side);
    if !(r.1[0] is Rejected) {
        lemma_submit(s, side, px, qty, tif);
        lemma_make_id(s.next_seq, s.free[0]);
        if tif is Fok {
            lemma_inv_book(s, ms);
            let free0 = s.free.drop_first();
            assert forall|k: int| 0 <= k < free0.len() implies (#[trigger] free0[k]) < SLOT_SPACE by {
                assert(free0[k] == s.free[k + 1]);
            }
            lemma_fillable_ge(s.ticks, ms, book(s, ms), idx(s.ticks, ms, px), qty, make_id(s.next_seq, s.free[0]), free0);
            lemma_match_loop(s.ticks, ms, book(s, ms), idx(s.ticks, ms, px), qty, make_id(s.next_seq, s.free[0]), free0);
        }
    }
}

/// Replay is compositional: recovering from a snapshot taken after `a` and
/// replaying `b` gives the same state and the same events as replaying `a + b`.
pub proof fn theorem_replay_compose(s: SState, a: Seq<Command>, b: Seq<Command>)
    ensures ({
        let ra = replay(s, a);
        let rb = replay(ra.0, b);
        replay(s, a + b) == (rb.0, ra.1 + rb.1)
    }),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(Seq::<Event>::empty() + replay(s, b).1 =~= replay(s, b).1);
    } else {
        let r1 = step(s, a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        theorem_replay_compose(r1.0, a.drop_first(), b);
        let ra2 = replay(r1.0, a.drop_first());
        let rb = replay(ra2.0, b);
        assert(r1.1 + (ra2.1 + rb.1) =~= (r1.1 + ra2.1) + rb.1);
    }
}

/// The invariant holds along every replay.
pub proof fn theorem_replay_inv(s: SState, log: Seq<Command>)
    requires inv(s),
    ensures inv(replay(s, log).0),
    decreases log.len(),
{
    if log.len() > 0 {
        theorem_inv(s, log[0]);
        theorem_replay_inv(step(s, log[0]).0, log.drop_first());
    }
}

pub proof fn theorem_init(ticks: u32, cap: u32)
    requires 1 <= ticks <= MAX_TICKS, cap <= MAX_CAPACITY,
    ensures inv(init(ticks, cap)),
{
}

} // verus!
