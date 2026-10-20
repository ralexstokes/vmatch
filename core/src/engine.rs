//! The matching engine. `Engine::step` is proven to compute exactly
//! `spec::step` on `Engine::view()`, and to preserve `Engine::wf()`, which
//! includes the model invariant `spec::inv`. Together with the theorems in
//! `props.rs` this gives the engine's guarantees.

use vstd::prelude::*;
use alloc::vec::Vec;
use crate::types::*;
use crate::spec::*;
use crate::props::*;
use crate::flat::*;
use crate::arena::*;

verus! {

pub struct Engine {
    ticks: u32,
    cap: u32,
    nodes: Vec<Node>,
    free_head: u32,
    free: Ghost<Seq<u32>>,
    bids: Ladder,
    asks: Ladder,
    next_seq: u64,
}

// ---------------------------------------------------------------------------
// Partition: every live node is a member of the level its price says.

pub open spec fn in_lad(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32, s: int) -> bool {
    let n = nodes[s];
    &&& 0 <= idx(ticks, side, n.price) < ticks
    &&& lad.lists@[idx(ticks, side, n.price)].contains(s as u32)
}

pub open spec fn side_partition(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32) -> bool {
    forall|s: int| 0 <= s < nodes.len() && (#[trigger] nodes[s]).live && nodes[s].side == side
        ==> in_lad(nodes, lad, side, ticks, s)
}

pub open spec fn lad_of(e: Engine, side: Side) -> Ladder {
    match side {
        Side::Buy => e.bids,
        Side::Sell => e.asks,
    }
}

impl Engine {
    pub closed spec fn view(&self) -> SState {
        SState {
            ticks: self.ticks,
            bids: side_view(self.nodes@, self.bids),
            asks: side_view(self.nodes@, self.asks),
            free: self.free@,
            next_seq: self.next_seq,
        }
    }

    pub closed spec fn wf_core(&self) -> bool {
        &&& 1 <= self.ticks <= MAX_TICKS
        &&& 1 <= self.cap <= MAX_CAPACITY
        &&& self.nodes@.len() == self.cap
        &&& self.next_seq <= MAX_SEQ + 1
        &&& ladder_wf(self.nodes@, self.bids, Side::Buy, self.ticks)
        &&& ladder_wf(self.nodes@, self.asks, Side::Sell, self.ticks)
        &&& free_wf(self.nodes@, self.free_head, self.free@)
        &&& side_partition(self.nodes@, self.bids, Side::Buy, self.ticks)
        &&& side_partition(self.nodes@, self.asks, Side::Sell, self.ticks)
    }

    /// The engine invariant. It includes the model invariant of its view.
    pub closed spec fn wf(&self) -> bool {
        self.wf_core() && inv(self.view())
    }
}

// ---------------------------------------------------------------------------
// Lemmas connecting the concrete ladder to the flat view.

proof fn lemma_side_view_facts(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32)
    requires ladder_wf(nodes, lad, side, ticks), 1 <= ticks,
    ensures
        (side_view(nodes, lad).len() > 0) == (lad.best < ticks),
        lad.best < ticks ==> {
            let L = ladder_view(nodes, lad.lists@);
            &&& side_view(nodes, lad) =~= L[lad.best as int] + flat(L.skip(lad.best + 1))
            &&& side_view(nodes, lad)[0] == ord(nodes[lad.lists@[lad.best as int][0] as int])
            &&& idx(ticks, side, side_view(nodes, lad)[0].price) == lad.best
        },
{
    let L = ladder_view(nodes, lad.lists@);
    lemma_ladder_indexed(nodes, lad, side, ticks);
    if lad.best < ticks {
        assert forall|t: int| 0 <= t < lad.best implies (#[trigger] L[t]).len() == 0 by {
            assert(lad.lists@[t].len() == 0);
        }
        lemma_flat_best(L, lad.best as int);
        lemma_member(nodes, lad, side, ticks, lad.best as int, 0);
    } else {
        assert forall|t: int| 0 <= t < L.len() implies (#[trigger] L[t]).len() == 0 by {
            assert(lad.lists@[t].len() == 0);
        }
        lemma_flat_all_empty(L);
    }
}

/// Position of a member in the flat view.
pub open spec fn flat_pos(L: Seq<Seq<SOrder>>, t: int, i: int) -> int {
    flat(L.take(t)).len() + i
}

proof fn lemma_flat_pos(L: Seq<Seq<SOrder>>, t: int, i: int)
    requires 0 <= t < L.len(), 0 <= i < L[t].len(),
    ensures
        0 <= flat_pos(L, t, i) < flat(L).len(),
        flat(L)[flat_pos(L, t, i)] == L[t][i],
        flat(L.update(t, L[t].remove(i))) =~= flat(L).remove(flat_pos(L, t, i)),
{
    lemma_flat_update(L, t, L[t].remove(i));
}

proof fn lemma_flat_pos_update(L: Seq<Seq<SOrder>>, t: int, i: int, o: SOrder)
    requires 0 <= t < L.len(), 0 <= i < L[t].len(),
    ensures flat(L.update(t, L[t].update(i, o))) =~= flat(L).update(flat_pos(L, t, i), o),
{
    lemma_flat_update(L, t, L[t].update(i, o));
}

/// Every element of the flat view is some member's order.
proof fn lemma_flat_member(L: Seq<Seq<SOrder>>, k: int) -> (r: (int, int))
    requires 0 <= k < flat(L).len(),
    ensures 0 <= r.0 < L.len(), 0 <= r.1 < L[r.0].len(), flat(L)[k] == L[r.0][r.1],
    decreases L.len(),
{
    if k < L[0].len() {
        (0, k)
    } else {
        let r = lemma_flat_member(L.drop_first(), k - L[0].len());
        (r.0 + 1, r.1)
    }
}

// ---------------------------------------------------------------------------
// Small exec helpers.

fn opp_exec(side: Side) -> (r: Side)
    ensures r == opp(side),
{
    match side {
        Side::Buy => Side::Sell,
        Side::Sell => Side::Buy,
    }
}

fn is_buy(side: Side) -> (r: bool)
    ensures r == (side is Buy),
{
    match side {
        Side::Buy => true,
        Side::Sell => false,
    }
}

fn rests_exec(tif: Tif) -> (r: bool)
    ensures r == rests(tif),
{
    match tif {
        Tif::Gtc | Tif::PostOnly => true,
        _ => false,
    }
}

fn market_price_exec(ticks: u32, side: Side) -> (r: u32)
    requires ticks >= 1,
    ensures r == market_price(ticks, side),
{
    match side {
        Side::Buy => ticks - 1,
        Side::Sell => 0,
    }
}

// ---------------------------------------------------------------------------
// Matching loop over one ladder.

pub fn match_exec(
    nodes: &mut Vec<Node>,
    lad: &mut Ladder,
    free_head: &mut u32,
    free: &mut Ghost<Seq<u32>>,
    ms: Side,
    ticks: u32,
    lim: u32,
    qty: u64,
    taker: u64,
    out: &mut Vec<Event>,
) -> (rem: u64)
    requires
        ladder_wf(old(nodes)@, *old(lad), ms, ticks),
        free_wf(old(nodes)@, *old(free_head), old(free)@),
        side_partition(old(nodes)@, *old(lad), ms, ticks),
        1 <= ticks,
        lim < ticks,
    ensures ({
        let r = match_loop(ticks, ms, side_view(old(nodes)@, *old(lad)), lim as int, qty, taker, old(free)@);
        &&& side_view(nodes@, *lad) == r.0
        &&& rem == r.1
        &&& out@ == old(out)@ + r.2
        &&& free@ == r.3
        &&& ladder_wf(nodes@, *lad, ms, ticks)
        &&& free_wf(nodes@, *free_head, free@)
        &&& side_partition(nodes@, *lad, ms, ticks)
        &&& frame(old(nodes)@, nodes@, ms, -1)
        &&& forall|s: int| 0 <= s < nodes@.len() ==> (#[trigger] nodes@[s]).live ==> old(nodes)@[s].live
        &&& forall|s: int| 0 <= s < nodes@.len() ==> #[trigger] nodes@[s].side == old(nodes)@[s].side
        &&& forall|s: int| 0 <= s < nodes@.len() ==> #[trigger] nodes@[s].price == old(nodes)@[s].price
        &&& forall|x: u32| #[trigger] free@.contains(x) ==> old(free)@.contains(x)
            || (old(nodes)@[x as int].live && old(nodes)@[x as int].side == ms)
    }),
{
    let ghost n0 = nodes@;
    let ghost f0 = free@;
    let ghost out0 = out@;
    let ghost r_all = match_loop(ticks, ms, side_view(n0, *lad), lim as int, qty, taker, f0);
    let ghost mut fills: Seq<Event> = Seq::empty();
    let mut rem = qty;
    proof {
        assert(fills + r_all.2 =~= r_all.2);
    }
    loop
        invariant
            1 <= ticks,
            lim < ticks,
            ladder_wf(nodes@, *lad, ms, ticks),
            free_wf(nodes@, *free_head, free@),
            side_partition(nodes@, *lad, ms, ticks),
            frame(n0, nodes@, ms, -1),
            forall|s: int| 0 <= s < nodes@.len() ==> (#[trigger] nodes@[s]).live ==> n0[s].live,
            forall|s: int| 0 <= s < nodes@.len() ==> #[trigger] nodes@[s].side == n0[s].side,
            forall|s: int| 0 <= s < nodes@.len() ==> #[trigger] nodes@[s].price == n0[s].price,
            forall|x: u32| #[trigger] free@.contains(x) ==> f0.contains(x) || (n0[x as int].live && n0[x as int].side == ms),
            out@ == out0 + fills,
            ({
                let c = match_loop(ticks, ms, side_view(nodes@, *lad), lim as int, rem, taker, free@);
                r_all == (c.0, c.1, fills + c.2, c.3)
            }),
        decreases side_view(nodes@, *lad).len() + (if rem > 0 { 1int } else { 0int }),
    {
        let ghost bk = side_view(nodes@, *lad);
        proof { lemma_side_view_facts(nodes@, *lad, ms, ticks); }
        if rem == 0 {
            break;
        }
        let b = lad.best;
        if b >= ticks || b > lim {
            break;
        }
        let ghost L = ladder_view(nodes@, lad.lists@);
        let h = lad.levels[b as usize].head;
        proof {
            assert(level_wf(nodes@, lad.levels@[b as int], lad.lists@[b as int], ms, b as int, ticks));
            lemma_member(nodes@, *lad, ms, ticks, b as int, 0);
            assert(h == lad.lists@[b as int][0]);
        }
        let m = nodes[h as usize];
        let ghost mo = ord(m);
        proof {
            assert(bk[0] == mo);
            assert(crosses(ticks, ms, bk[0], lim as int));
            // h is live, hence not on the free stack
            if free@.contains(h) {
                let k = choose|k: int| 0 <= k < free@.len() && free@[k] == h;
                assert(!nodes@[free@[k] as int].live);
            }
        }
        if m.qty <= rem {
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: m.qty };
            out.push(ev);
            rem = rem - m.qty;
            let ghost n1 = nodes@;
            let ghost lad1 = *lad;
            unlink(nodes, lad, ms, ticks, b, h, Ghost(0));
            proof {
                lemma_free_frame(n1, nodes@, *free_head, free@);
            }
            let g = free_push(nodes, free_head, Ghost(free@), h);
            *free = g;
            proof {
                let n2 = nodes@;
                lemma_ladder_frame_one(n1, n2, *lad, ms, ticks, h as int);
                lemma_flat_pos(L, b as int, 0);
                assert(flat_pos(L, b as int, 0) == 0) by {
                    lemma_flat_take_empty(L, b as int);
                }
                assert(side_view(n2, *lad) =~= bk.remove(0));
                assert(bk.remove(0) =~= bk.drop_first());
                assert(slot_of(m.id) == h as int);
                fills = fills + seq![ev];
                // the remaining computation unfolds by one step
                assert(match_loop(ticks, ms, bk, lim as int, (rem + m.qty) as u64, taker, free@.drop_first())
                    == ({
                        let r = match_loop(ticks, ms, bk.drop_first(), lim as int, rem, taker, seq![h] + free@.drop_first());
                        (r.0, r.1, seq![ev] + r.2, r.3)
                    }));
                assert(free@ =~= seq![h] + free@.drop_first());
                assert(fills.drop_last() + (seq![ev] + match_loop(ticks, ms, bk.drop_first(), lim as int, rem, taker, free@).2)
                    =~= fills + match_loop(ticks, ms, bk.drop_first(), lim as int, rem, taker, free@).2);
                lemma_partition_after_unlink(n1, n2, lad1, *lad, ms, ticks, b as int, h);
                assert forall|x: u32| #[trigger] free@.contains(x) implies f0.contains(x) || (n0[x as int].live && n0[x as int].side == ms) by {
                    if x == h {
                    } else {
                        assert(free@.drop_first().contains(x)) by {
                            let k = choose|k: int| 0 <= k < free@.len() && free@[k] == x;
                            assert(free@.drop_first()[k - 1] == x);
                        }
                    }
                }
            }
        } else {
            let ev = Event::Fill { taker, maker: m.id, price: m.price, qty: rem };
            out.push(ev);
            let ghost n1 = nodes@;
            set_qty(nodes, lad, ms, ticks, b, h, Ghost(0), m.qty - rem);
            proof {
                let n2 = nodes@;
                lemma_flat_pos_update(L, b as int, 0, SOrder { qty: (m.qty - rem) as u64, ..L[b as int][0] });
                assert(flat_pos(L, b as int, 0) == 0) by {
                    lemma_flat_take_empty(L, b as int);
                }
                lemma_free_frame(n1, n2, *free_head, free@);
                fills = fills + seq![ev];
                assert(match_loop(ticks, ms, bk, lim as int, rem, taker, free@)
                    == (bk.update(0, SOrder { qty: (m.qty - rem) as u64, ..mo }), 0u64, seq![ev], free@));
                lemma_partition_frame(n1, n2, *lad, ms, ticks);
            }
            rem = 0;
            proof {
                assert(match_loop(ticks, ms, side_view(nodes@, *lad), lim as int, rem, taker, free@).2 =~= Seq::<Event>::empty());
                assert(fills + Seq::<Event>::empty() =~= fills);
            }
        }
    }
    proof {
        lemma_side_view_facts(nodes@, *lad, ms, ticks);
        assert(match_loop(ticks, ms, side_view(nodes@, *lad), lim as int, rem, taker, free@).2 =~= Seq::<Event>::empty());
        assert(fills + Seq::<Event>::empty() =~= fills);
    }
    rem
}

proof fn lemma_flat_take_empty(L: Seq<Seq<SOrder>>, b: int)
    requires 0 <= b <= L.len(), forall|t: int| 0 <= t < b ==> (#[trigger] L[t]).len() == 0,
    ensures flat(L.take(b)).len() == 0,
{
    assert forall|t: int| 0 <= t < L.take(b).len() implies (#[trigger] L.take(b)[t]).len() == 0 by {
        assert(L.take(b)[t] == L[t]);
    }
    lemma_flat_all_empty(L.take(b));
}

/// After a ladder op that only touched one dead node outside the ladder.
proof fn lemma_ladder_frame_one(n1: Seq<Node>, n2: Seq<Node>, lad: Ladder, side: Side, ticks: u32, x: int)
    requires
        ladder_wf(n1, lad, side, ticks),
        n1.len() == n2.len(),
        0 <= x < n1.len(),
        !n1[x].live,
        forall|s: int| 0 <= s < n1.len() && s != x ==> #[trigger] n2[s] == n1[s],
    ensures
        ladder_wf(n2, lad, side, ticks),
        ladder_view(n2, lad.lists@) =~= ladder_view(n1, lad.lists@),
        side_view(n2, lad) == side_view(n1, lad),
{
    lemma_ladder_frame(n1, n2, lad, side, ticks);
}

proof fn lemma_partition_frame(n1: Seq<Node>, n2: Seq<Node>, lad: Ladder, side: Side, ticks: u32)
    requires
        side_partition(n1, lad, side, ticks),
        n1.len() == n2.len(),
        forall|s: int| 0 <= s < n1.len() ==> (#[trigger] n2[s]).live == n1[s].live && n2[s].side == n1[s].side && n2[s].price == n1[s].price,
    ensures side_partition(n2, lad, side, ticks),
{
    assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == side
        implies in_lad(n2, lad, side, ticks, s) by {
        assert(n1[s].live);
        assert(in_lad(n1, lad, side, ticks, s));
    }
}

proof fn lemma_partition_after_unlink(n1: Seq<Node>, n2: Seq<Node>, lad1: Ladder, lad2: Ladder, side: Side, ticks: u32, t: int, h: u32)
    requires
        side_partition(n1, lad1, side, ticks),
        n1.len() == n2.len(),
        0 <= t < ticks,
        lad1.lists@.len() == ticks,
        lad2.lists@ == lad1.lists@.update(t, lad1.lists@[t].remove(0)),
        lad1.lists@[t].len() > 0,
        lad1.lists@[t][0] == h,
        !n2[h as int].live,
        forall|s: int| 0 <= s < n1.len() && s != h ==> (#[trigger] n2[s]).live == n1[s].live && n2[s].side == n1[s].side && n2[s].price == n1[s].price,
    ensures side_partition(n2, lad2, side, ticks),
{
    lemma_partition_after_remove(n1, n2, lad1, lad2, side, ticks, t, 0, h);
}

proof fn lemma_partition_after_remove(n1: Seq<Node>, n2: Seq<Node>, lad1: Ladder, lad2: Ladder, side: Side, ticks: u32, t: int, i: int, h: u32)
    requires
        side_partition(n1, lad1, side, ticks),
        n1.len() == n2.len(),
        0 <= t < ticks,
        lad1.lists@.len() == ticks,
        0 <= i < lad1.lists@[t].len(),
        lad2.lists@ == lad1.lists@.update(t, lad1.lists@[t].remove(i)),
        lad1.lists@[t][i] == h,
        !n2[h as int].live,
        forall|s: int| 0 <= s < n1.len() && s != h ==> (#[trigger] n2[s]).live == n1[s].live && n2[s].side == n1[s].side && n2[s].price == n1[s].price,
    ensures side_partition(n2, lad2, side, ticks),
{
    assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == side
        implies in_lad(n2, lad2, side, ticks, s) by {
        assert(s != h);
        assert(n1[s].live);
        assert(in_lad(n1, lad1, side, ticks, s));
        let tt = idx(ticks, side, n1[s].price);
        let l = lad1.lists@[tt];
        let k = choose|k: int| 0 <= k < l.len() && l[k] == s as u32;
        if tt == t {
            let l2 = l.remove(i);
            if k < i { assert(l2[k] == s as u32); } else { assert(k != i); assert(l2[k - 1] == s as u32); }
        }
    }
}

// ---------------------------------------------------------------------------
// The engine.

impl Engine {
    /// A new, empty engine for prices `0..ticks` with room for `cap` resting
    /// orders.
    pub fn new(ticks: u32, cap: u32) -> (e: Engine)
        requires 1 <= ticks <= MAX_TICKS, 1 <= cap <= MAX_CAPACITY,
        ensures e.wf(), e.view() == init(ticks, cap),
    {
        let mut nodes: Vec<Node> = Vec::with_capacity(cap as usize);
        let mut i: u32 = 0;
        while i < cap
            invariant
                i <= cap,
                cap <= MAX_CAPACITY,
                nodes@.len() == i,
                forall|k: int| 0 <= k < i ==> (#[trigger] nodes@[k]).live == false
                    && nodes@[k].next == (if k + 1 < cap { (k + 1) as u32 } else { NIL }),
            decreases cap - i,
        {
            let next = if i + 1 < cap { i + 1 } else { NIL };
            nodes.push(Node { id: 0, qty: 0, next, prev: NIL, price: 0, side: Side::Buy, live: false });
            i = i + 1;
        }
        let mut bl: Vec<Level> = Vec::with_capacity(ticks as usize);
        let mut al: Vec<Level> = Vec::with_capacity(ticks as usize);
        let mut t: u32 = 0;
        while t < ticks
            invariant
                t <= ticks,
                bl@.len() == t,
                al@.len() == t,
                forall|k: int| 0 <= k < t ==> (#[trigger] bl@[k]) == (Level { head: NIL, tail: NIL }),
                forall|k: int| 0 <= k < t ==> (#[trigger] al@[k]) == (Level { head: NIL, tail: NIL }),
            decreases ticks - t,
        {
            bl.push(Level { head: NIL, tail: NIL });
            al.push(Level { head: NIL, tail: NIL });
            t = t + 1;
        }
        let ghost empty_lists: Seq<Seq<u32>> = Seq::new(ticks as nat, |k: int| Seq::<u32>::empty());
        let e = Engine {
            ticks,
            cap,
            nodes,
            free_head: 0,
            free: Ghost(Seq::new(cap as nat, |k: int| k as u32)),
            bids: Ladder { levels: bl, best: ticks, lists: Ghost(empty_lists) },
            asks: Ladder { levels: al, best: ticks, lists: Ghost(empty_lists) },
            next_seq: 0,
        };
        proof {
            let f = e.free@;
            assert forall|a: int, b: int| 0 <= a < f.len() && 0 <= b < f.len() && a != b implies f[a] != f[b] by {}
            assert forall|k: int| 0 <= k < f.len() implies {
                &&& ((#[trigger] f[k]) as int) < e.nodes@.len()
                &&& !e.nodes@[f[k] as int].live
                &&& e.nodes@[f[k] as int].next == next_of(f, k)
            } by {}
            assert forall|tt: int| 0 <= tt < ticks implies #[trigger] level_wf(e.nodes@, e.bids.levels@[tt], e.bids.lists@[tt], Side::Buy, tt, ticks) by {}
            assert forall|tt: int| 0 <= tt < ticks implies #[trigger] level_wf(e.nodes@, e.asks.levels@[tt], e.asks.lists@[tt], Side::Sell, tt, ticks) by {}
            lemma_ladder_indexed(e.nodes@, e.bids, Side::Buy, ticks);
            lemma_ladder_indexed(e.nodes@, e.asks, Side::Sell, ticks);
            assert forall|tt: int| 0 <= tt < ticks implies (#[trigger] ladder_view(e.nodes@, e.bids.lists@)[tt]).len() == 0 by {}
            assert forall|tt: int| 0 <= tt < ticks implies (#[trigger] ladder_view(e.nodes@, e.asks.lists@)[tt]).len() == 0 by {}
            lemma_flat_all_empty(ladder_view(e.nodes@, e.bids.lists@));
            lemma_flat_all_empty(ladder_view(e.nodes@, e.asks.lists@));
            assert(e.view().free =~= init(ticks, cap).free);
            assert(e.view() =~= init(ticks, cap));
            theorem_init(ticks, cap);
        }
        e
    }

    /// Checked constructor for unverified callers.
    pub fn try_new(ticks: u32, cap: u32) -> (r: Option<Engine>)
        ensures r matches Some(e) ==> e.wf() && e.view() == init(ticks, cap),
    {
        if 1 <= ticks && ticks <= MAX_TICKS && 1 <= cap && cap <= MAX_CAPACITY {
            Some(Engine::new(ticks, cap))
        } else {
            None
        }
    }

    pub fn ticks(&self) -> (r: u32)
        requires self.wf(),
        ensures r == self.view().ticks,
    {
        self.ticks
    }

    /// Best bid price, if any.
    pub fn best_bid(&self) -> (r: Option<u32>)
        requires self.wf(),
        ensures
            r is None <==> self.view().bids.len() == 0,
            r matches Some(p) ==> p == self.view().bids[0].price,
    {
        proof { lemma_side_view_facts(self.nodes@, self.bids, Side::Buy, self.ticks); }
        if self.bids.best < self.ticks {
            Some(self.ticks - 1 - self.bids.best)
        } else {
            None
        }
    }

    /// Best ask price, if any.
    pub fn best_ask(&self) -> (r: Option<u32>)
        requires self.wf(),
        ensures
            r is None <==> self.view().asks.len() == 0,
            r matches Some(p) ==> p == self.view().asks[0].price,
    {
        proof { lemma_side_view_facts(self.nodes@, self.asks, Side::Sell, self.ticks); }
        if self.asks.best < self.ticks {
            Some(self.asks.best)
        } else {
            None
        }
    }

    /// Apply one command, appending its events to `out`.
    pub fn step(&mut self, cmd: Command, out: &mut Vec<Event>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.view() == step(old(self).view(), cmd).0,
            out@ == old(out)@ + step(old(self).view(), cmd).1,
    {
        let ghost s0 = self.view();
        match cmd {
            Command::New { side, ord_type, tif, price, qty } => self.exec_new(side, ord_type, tif, price, qty, out),
            Command::Cancel { id } => self.exec_cancel(id, out),
            Command::Replace { id, price, qty, post_only } => self.exec_replace(id, price, qty, post_only, out),
        }
        proof {
            theorem_inv(s0, cmd);
        }
    }

    fn reject(&self, r: RejectReason, out: &mut Vec<Event>)
        ensures out@ == old(out)@ + seq![Event::Rejected { reason: r }],
    {
        out.push(Event::Rejected { reason: r });
        proof { assert(out@ =~= old(out)@ + seq![Event::Rejected { reason: r }]); }
    }

    /// O(1): does a taker at index `lim` on the maker side cross the best maker?
    fn would_cross_exec(&self, ms: Side, lim: u32) -> (r: bool)
        requires self.wf_core(), lim < self.ticks,
        ensures r == (book(self.view(), ms).len() > 0 && crosses(self.ticks, ms, book(self.view(), ms)[0], lim as int)),
    {
        let lad = if is_buy(ms) { &self.bids } else { &self.asks };
        proof { lemma_side_view_facts(self.nodes@, *lad, ms, self.ticks); }
        lad.best < self.ticks && lad.best <= lim
    }

    /// Is the crossing liquidity on the maker side at least `qty`?
    fn fok_exec(&self, ms: Side, lim: u32, qty: u64) -> (r: bool)
        requires self.wf_core(), lim < self.ticks, valid_qty(qty),
        ensures r == (fillable(self.ticks, ms, book(self.view(), ms), lim as int) >= qty),
    {
        let lad = if is_buy(ms) { &self.bids } else { &self.asks };
        let ghost L = ladder_view(self.nodes@, lad.lists@);
        let ticks = self.ticks;
        proof {
            lemma_ladder_indexed(self.nodes@, *lad, ms, ticks);
            lemma_fillable_flat(ticks, ms, L, lim as int);
            lemma_flat_take_empty(L, lad.best as int);
            assert(qsum(flat(L.take(lad.best as int))) == 0);
        }
        let mut acc: u64 = 0;
        let mut t = lad.best;
        while t < ticks && t <= lim
            invariant
                ladder_wf(self.nodes@, *lad, ms, ticks),
                L == ladder_view(self.nodes@, lad.lists@),
                lad.best <= t <= ticks,
                t <= lim + 1,
                lim < ticks,
                valid_qty(qty),
                acc as int == qsum(flat(L.take(t as int))),
                acc < qty,
            decreases ticks - t,
        {
            let mut cur = lad.levels[t as usize].head;
            let ghost l = lad.lists@[t as int];
            let ghost mut i: int = 0;
            proof {
                assert(level_wf(self.nodes@, lad.levels@[t as int], l, ms, t as int, ticks));
                assert(L[t as int].take(0) =~= Seq::<SOrder>::empty());
            }
            while cur != NIL
                invariant
                    ladder_wf(self.nodes@, *lad, ms, ticks),
                    L == ladder_view(self.nodes@, lad.lists@),
                    t < ticks,
                    l == lad.lists@[t as int],
                    level_wf(self.nodes@, lad.levels@[t as int], l, ms, t as int, ticks),
                    0 <= i <= l.len(),
                    cur == (if i < l.len() { l[i] } else { NIL }),
                    valid_qty(qty),
                    acc as int == qsum(flat(L.take(t as int))) + qsum(L[t as int].take(i)),
                    acc < qty,
                decreases l.len() - i,
            {
                proof {
                    assert(member_ok(self.nodes@, l, i, ms, t as int, ticks));
                    assert(L[t as int][i] == ord(self.nodes@[l[i] as int]));
                    lemma_qsum_take_step(L[t as int], i);
                }
                let n = self.nodes[cur as usize];
                acc = acc + n.qty;
                if acc >= qty {
                    proof {
                        lemma_fok_lower_bound(L, t as int, i + 1, lim as int);
                    }
                    return true;
                }
                cur = n.next;
                proof { i = i + 1; }
            }
            proof {
                assert(L[t as int].take(i) =~= L[t as int]);
                lemma_flat_len_take(L, t as int);
                lemma_qsum_add(flat(L.take(t as int)), L[t as int]);
            }
            t = t + 1;
        }
        proof {
            let n = if lim as int + 1 < L.len() { lim as int + 1 } else { L.len() as int };
            assert(t as int == n);
        }
        false
    }

    /// Allocate an id, match, then rest or expire. Mirrors `spec::submit`.
    fn submit_exec(&mut self, side: Side, price: u32, qty: u64, tif: Tif, out: &mut Vec<Event>)
        requires
            old(self).wf_core(),
            inv(old(self).view()),
            submit_ok(old(self).view(), side, price, qty, tif),
        ensures
            self.wf_core(),
            self.view() == submit(old(self).view(), side, price, qty, tif).0,
            out@ == old(out)@ + submit(old(self).view(), side, price, qty, tif).1,
    {
        let ghost s0 = self.view();
        let ghost out0 = out@;
        let ticks = self.ticks;
        let (slot, fg) = free_pop(&self.nodes, &mut self.free_head, Ghost(self.free@));
        self.free = fg;
        proof {
            assert(slot < SLOT_SPACE);
            lemma_make_id(self.next_seq, slot);
        }
        let id = self.next_seq * SLOT_SPACE + slot as u64;
        proof { assert(id == make_id(s0.next_seq, s0.free[0])); }

        out.push(Event::Accepted { id, side, price, qty });
        let ms = opp_exec(side);
        let lim = level_index(ticks, ms, price);
        let ghost n0 = self.nodes@;
        let ghost bids0 = self.bids;
        let ghost asks0 = self.asks;
        let ghost f1 = self.free@;
        let rem;
        if is_buy(ms) {
            rem = match_exec(&mut self.nodes, &mut self.bids, &mut self.free_head, &mut self.free, ms, ticks, lim, qty, id, out);
            proof {
                lemma_ladder_frame(n0, self.nodes@, self.asks, Side::Sell, ticks);
                lemma_partition_other(n0, self.nodes@, self.asks, Side::Sell, Side::Buy, ticks);
            }
        } else {
            rem = match_exec(&mut self.nodes, &mut self.asks, &mut self.free_head, &mut self.free, ms, ticks, lim, qty, id, out);
            proof {
                lemma_ladder_frame(n0, self.nodes@, self.bids, Side::Buy, ticks);
                lemma_partition_other(n0, self.nodes@, self.bids, Side::Buy, Side::Sell, ticks);
            }
        }
        let ghost mr = match_loop(ticks, ms, book(s0, ms), lim as int, qty, id, s0.free.drop_first());
        proof {
            assert(book(s0, ms) == side_view(n0, lad_of(*old(self), ms)));
            assert(rem == mr.1);
            assert(self.free@ == mr.3);
            // the in-flight taker slot is untouched: dead, unlisted, not free
            assert(!n0[slot as int].live);
            assert(self.nodes@[slot as int] == n0[slot as int]);
            assert(!self.free@.contains(slot)) by {
                if self.free@.contains(slot) {
                    assert(f1.contains(slot) || n0[slot as int].live);
                }
            }
        }
        let ghost n1 = self.nodes@;
        let ghost e_mid = *self;
        if rem > 0 && rests_exec(tif) {
            let t = level_index(ticks, side, price);
            if is_buy(side) {
                push_back(&mut self.nodes, &mut self.bids, side, ticks, t, slot, id, price, rem);
                proof {
                    lemma_ladder_frame(n1, self.nodes@, self.asks, Side::Sell, ticks);
                }
            } else {
                push_back(&mut self.nodes, &mut self.asks, side, ticks, t, slot, id, price, rem);
                proof {
                    lemma_ladder_frame(n1, self.nodes@, self.bids, Side::Buy, ticks);
                }
            }
            out.push(Event::Rested { id, qty: rem });
            proof {
                let n2 = self.nodes@;
                lemma_free_after_push_back(n1, n2, self.free_head, self.free@, slot);
                lemma_partition_after_push(n1, n2, e_mid, *self, side, ticks, slot, t);
                let L = ladder_view(n1, lad_of(*old(self), side).lists@);
                lemma_ladder_indexed(n0, lad_of(*old(self), side), side, ticks);
                lemma_ladder_frame(n0, n1, lad_of(*old(self), side), side, ticks);
                lemma_flat_push_level(ticks, side, L, t as int, SOrder { id, price, qty: rem });
            }
        } else {
            if rem > 0 {
                out.push(Event::Expired { id, qty: rem });
            }
            let g = free_push(&mut self.nodes, &mut self.free_head, Ghost(self.free@), slot);
            self.free = g;
            proof {
                let n2 = self.nodes@;
                lemma_ladder_frame_one(n1, n2, self.bids, Side::Buy, ticks, slot as int);
                lemma_ladder_frame_one(n1, n2, self.asks, Side::Sell, ticks, slot as int);
                lemma_partition_frame(n1, n2, self.bids, Side::Buy, ticks);
                lemma_partition_frame(n1, n2, self.asks, Side::Sell, ticks);
                lemma_ladder_frame(n0, n1, lad_of(*old(self), side), side, ticks);
            }
        }
        self.next_seq = self.next_seq + 1;
        proof {
            let r = submit(s0, side, price, qty, tif);
            assert(self.view() =~= r.0);
            assert(out@ =~= out0 + r.1);
        }
    }

    fn exec_new(&mut self, side: Side, ord_type: OrdType, tif: Tif, price: u32, qty: u64, out: &mut Vec<Event>)
        requires old(self).wf(),
        ensures
            self.wf_core(),
            self.view() == step_new(old(self).view(), side, ord_type, tif, price, qty).0,
            out@ == old(out)@ + step_new(old(self).view(), side, ord_type, tif, price, qty).1,
    {
        let market = match ord_type { OrdType::Market => true, OrdType::Limit => false };
        if market {
            match tif {
                Tif::Ioc | Tif::Fok => {},
                _ => { self.reject(RejectReason::InvalidTif, out); return; },
            }
        }
        if !market && price >= self.ticks {
            self.reject(RejectReason::InvalidPrice, out);
            return;
        }
        if qty == 0 || qty > MAX_QTY {
            self.reject(RejectReason::InvalidQty, out);
            return;
        }
        if self.next_seq > MAX_SEQ {
            self.reject(RejectReason::SeqExhausted, out);
            return;
        }
        proof {
            if self.free@.len() > 0 { assert((self.free@[0] as int) < self.nodes@.len()); }
        }
        if self.free_head == NIL {
            self.reject(RejectReason::BookFull, out);
            return;
        }
        let px = if market { market_price_exec(self.ticks, side) } else { price };
        let ms = opp_exec(side);
        let lim = level_index(self.ticks, ms, px);
        match tif {
            Tif::PostOnly => {
                if self.would_cross_exec(ms, lim) {
                    self.reject(RejectReason::WouldCross, out);
                    return;
                }
            },
            Tif::Fok => {
                if !self.fok_exec(ms, lim, qty) {
                    self.reject(RejectReason::FokUnfillable, out);
                    return;
                }
            },
            _ => {},
        }
        self.submit_exec(side, px, qty, tif, out);
    }

    /// Locate a live order by id in O(1): the id encodes its arena slot.
    fn lookup(&self, id: u64) -> (r: Option<u32>)
        requires self.wf(),
        ensures
            r is None ==> find(self.view(), id) is None,
            r matches Some(slot) ==> {
                let n = self.nodes@[slot as int];
                &&& (slot as int) < self.nodes@.len()
                &&& n.live
                &&& n.id == id
                &&& find(self.view(), id) == Some((n.side, flat_pos(
                        ladder_view(self.nodes@, lad_of(*self, n.side).lists@),
                        idx(self.ticks, n.side, n.price),
                        lad_of(*self, n.side).lists@[idx(self.ticks, n.side, n.price)].index_of(slot))))
                &&& lad_of(*self, n.side).lists@[idx(self.ticks, n.side, n.price)].contains(slot)
            },
    {
        let s64 = id % SLOT_SPACE;
        proof { lemma_lookup_none(*self, id); }
        if s64 >= self.cap as u64 {
            return None;
        }
        let slot = s64 as u32;
        let n = self.nodes[slot as usize];
        if !n.live || n.id != id {
            return None;
        }
        proof { lemma_lookup_some(*self, id, slot); }
        Some(slot)
    }

    fn exec_cancel(&mut self, id: u64, out: &mut Vec<Event>)
        requires old(self).wf(),
        ensures
            self.wf_core(),
            self.view() == step_cancel(old(self).view(), id).0,
            out@ == old(out)@ + step_cancel(old(self).view(), id).1,
    {
        match self.lookup(id) {
            None => {
                self.reject(RejectReason::UnknownOrder, out);
            },
            Some(slot) => {
                let n = self.nodes[slot as usize];
                self.remove_exec(slot);
                out.push(Event::Cancelled { id, qty: n.qty });
                proof { assert(out@ =~= old(out)@ + seq![Event::Cancelled { id, qty: n.qty }]); }
            },
        }
    }

    /// Unlink a live order and free its slot. Mirrors `spec::remove_at`.
    fn remove_exec(&mut self, slot: u32)
        requires
            old(self).wf_core(),
            inv(old(self).view()),
            (slot as int) < old(self).nodes@.len(),
            old(self).nodes@[slot as int].live,
        ensures ({
            let n = old(self).nodes@[slot as int];
            let L = ladder_view(old(self).nodes@, lad_of(*old(self), n.side).lists@);
            let t = idx(old(self).ticks, n.side, n.price);
            let i = lad_of(*old(self), n.side).lists@[t].index_of(slot);
            &&& self.wf_core()
            &&& self.view() == remove_at(old(self).view(), n.side, flat_pos(L, t, i))
            &&& book(old(self).view(), n.side)[flat_pos(L, t, i)] == ord(n)
        }),
    {
        let ticks = self.ticks;
        let n = self.nodes[slot as usize];
        let t = level_index(ticks, n.side, n.price);
        let ghost s0 = self.view();
        let ghost n0 = self.nodes@;
        let ghost lad0 = lad_of(*self, n.side);
        let ghost l = lad0.lists@[t as int];
        let ghost i = l.index_of(slot);
        proof {
            assert(in_lad(n0, lad0, n.side, ticks, slot as int));
            l.index_of_first_ensures(slot);
            lemma_member(n0, lad0, n.side, ticks, t as int, i);
            // a live slot is not on the free stack
            if self.free@.contains(slot) {
                let k = choose|k: int| 0 <= k < self.free@.len() && self.free@[k] == slot;
                assert(!n0[self.free@[k] as int].live);
            }
        }
        if is_buy(n.side) {
            unlink(&mut self.nodes, &mut self.bids, n.side, ticks, t, slot, Ghost(i));
            proof {
                lemma_ladder_frame(n0, self.nodes@, self.asks, Side::Sell, ticks);
                lemma_partition_other(n0, self.nodes@, self.asks, Side::Sell, Side::Buy, ticks);
                lemma_partition_after_remove(n0, self.nodes@, lad0, self.bids, Side::Buy, ticks, t as int, i, slot);
            }
        } else {
            unlink(&mut self.nodes, &mut self.asks, n.side, ticks, t, slot, Ghost(i));
            proof {
                lemma_ladder_frame(n0, self.nodes@, self.bids, Side::Buy, ticks);
                lemma_partition_other(n0, self.nodes@, self.bids, Side::Buy, Side::Sell, ticks);
                lemma_partition_after_remove(n0, self.nodes@, lad0, self.asks, Side::Sell, ticks, t as int, i, slot);
            }
        }
        let ghost n1 = self.nodes@;
        proof { lemma_free_frame(n0, n1, self.free_head, self.free@); }
        let g = free_push(&mut self.nodes, &mut self.free_head, Ghost(self.free@), slot);
        self.free = g;
        proof {
            let n2 = self.nodes@;
            lemma_ladder_frame_one(n1, n2, self.bids, Side::Buy, ticks, slot as int);
            lemma_ladder_frame_one(n1, n2, self.asks, Side::Sell, ticks, slot as int);
            lemma_partition_frame(n1, n2, self.bids, Side::Buy, ticks);
            lemma_partition_frame(n1, n2, self.asks, Side::Sell, ticks);
            let L = ladder_view(n0, lad0.lists@);
            lemma_ladder_indexed(n0, lad0, n.side, ticks);
            lemma_flat_pos(L, t as int, i);
            assert(slot_of(n.id) == slot as int);
            assert(self.view() =~= remove_at(s0, n.side, flat_pos(L, t as int, i)));
        }
    }

    fn exec_replace(&mut self, id: u64, price: u32, qty: u64, post_only: bool, out: &mut Vec<Event>)
        requires old(self).wf(),
        ensures
            self.wf_core(),
            self.view() == step_replace(old(self).view(), id, price, qty, post_only).0,
            out@ == old(out)@ + step_replace(old(self).view(), id, price, qty, post_only).1,
    {
        let ghost s0 = self.view();
        if price >= self.ticks {
            self.reject(RejectReason::InvalidPrice, out);
            return;
        }
        if qty == 0 || qty > MAX_QTY {
            self.reject(RejectReason::InvalidQty, out);
            return;
        }
        let slot = match self.lookup(id) {
            None => {
                self.reject(RejectReason::UnknownOrder, out);
                return;
            },
            Some(slot) => slot,
        };
        let n = self.nodes[slot as usize];
        let ticks = self.ticks;
        let t = level_index(ticks, n.side, n.price);
        let ghost lad0 = lad_of(*self, n.side);
        let ghost i = lad0.lists@[t as int].index_of(slot);
        if price == n.price && qty <= n.qty {
            let ghost n0 = self.nodes@;
            proof {
                lad0.lists@[t as int].index_of_first_ensures(slot);
            }
            if is_buy(n.side) {
                set_qty(&mut self.nodes, &self.bids, n.side, ticks, t, slot, Ghost(i), qty);
                proof { lemma_ladder_frame(n0, self.nodes@, self.asks, Side::Sell, ticks); }
            } else {
                set_qty(&mut self.nodes, &self.asks, n.side, ticks, t, slot, Ghost(i), qty);
                proof { lemma_ladder_frame(n0, self.nodes@, self.bids, Side::Buy, ticks); }
            }
            out.push(Event::Reduced { id, from: n.qty, to: qty });
            proof {
                let n1 = self.nodes@;
                lemma_free_frame(n0, n1, self.free_head, self.free@);
                lemma_partition_frame(n0, n1, self.bids, Side::Buy, ticks);
                lemma_partition_frame(n0, n1, self.asks, Side::Sell, ticks);
                let L = ladder_view(n0, lad0.lists@);
                lemma_ladder_indexed(n0, lad0, n.side, ticks);
                lemma_flat_pos_update(L, t as int, i, SOrder { qty, ..L[t as int][i] });
                assert(out@ =~= old(out)@ + seq![Event::Reduced { id, from: n.qty, to: qty }]);
            }
            return;
        }
        if self.next_seq > MAX_SEQ {
            self.reject(RejectReason::SeqExhausted, out);
            return;
        }
        let ms = opp_exec(n.side);
        let lim = level_index(ticks, ms, price);
        if post_only && self.would_cross_exec(ms, lim) {
            self.reject(RejectReason::WouldCross, out);
            return;
        }
        let ghost out0 = out@;
        self.remove_exec(slot);
        out.push(Event::Cancelled { id, qty: n.qty });
        let ghost s1 = self.view();
        proof {
            lemma_remove_at(s0, n.side, flat_pos(ladder_view(old(self).nodes@, lad0.lists@), t as int, i));
            assert(book(s1, opp(n.side)) == book(s0, opp(n.side)));
        }
        let tif = if post_only { Tif::PostOnly } else { Tif::Gtc };
        self.submit_exec(n.side, price, qty, tif, out);
        proof {
            assert(out@ =~= out0 + (seq![Event::Cancelled { id, qty: n.qty }] + submit(s1, n.side, price, qty, tif).1));
        }
    }
}

// ---------------------------------------------------------------------------
// Remaining lemmas used above.

proof fn lemma_partition_other(n1: Seq<Node>, n2: Seq<Node>, lad: Ladder, side: Side, other: Side, ticks: u32)
    requires
        side_partition(n1, lad, side, ticks),
        side != other,
        frame(n1, n2, other, -1),
        forall|s: int| 0 <= s < n2.len() ==> (#[trigger] n2[s]).live ==> n1[s].live,
        forall|s: int| 0 <= s < n2.len() ==> #[trigger] n2[s].side == n1[s].side,
    ensures side_partition(n2, lad, side, ticks),
{
    assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == side
        implies in_lad(n2, lad, side, ticks, s) by {
        assert(n1[s].live);
        assert(n2[s] == n1[s]);
        assert(in_lad(n1, lad, side, ticks, s));
    }
}

proof fn lemma_qsum_take_step(l: Seq<SOrder>, i: int)
    requires 0 <= i < l.len(),
    ensures qsum(l.take(i + 1)) == qsum(l.take(i)) + l[i].qty,
{
    assert(l.take(i + 1) =~= l.take(i) + seq![l[i]]);
    lemma_qsum_add(l.take(i), seq![l[i]]);
    assert(seq![l[i]].drop_first() =~= Seq::<SOrder>::empty());
}

proof fn lemma_qsum_take_le(l: Seq<SOrder>, i: int)
    requires 0 <= i <= l.len(),
    ensures qsum(l.take(i)) <= qsum(l),
{
    assert(l =~= l.take(i) + l.skip(i));
    lemma_qsum_add(l.take(i), l.skip(i));
    lemma_qsum_nonneg(l.skip(i));
}

/// Early exit of the FOK scan is sound: the crossing prefix is at least what
/// has been summed so far.
proof fn lemma_fok_lower_bound(L: Seq<Seq<SOrder>>, t: int, i: int, lim: int)
    requires 0 <= t < L.len(), 0 <= i <= L[t].len(), t <= lim,
    ensures ({
        let n = if lim + 1 < L.len() { lim + 1 } else { L.len() as int };
        qsum(flat(L.take(n))) >= qsum(flat(L.take(t))) + qsum(L[t].take(i))
    }),
{
    let n = if lim + 1 < L.len() { lim + 1 } else { L.len() as int };
    let Ln = L.take(n);
    lemma_flat_split(Ln, t);
    assert(Ln.take(t) =~= L.take(t));
    assert(Ln[t] == L[t]);
    lemma_qsum_add(flat(Ln.take(t)) + Ln[t], flat(Ln.skip(t + 1)));
    lemma_qsum_add(flat(Ln.take(t)), Ln[t]);
    lemma_qsum_nonneg(flat(Ln.skip(t + 1)));
    lemma_qsum_take_le(L[t], i);
}

proof fn lemma_free_after_push_back(n1: Seq<Node>, n2: Seq<Node>, head: u32, f: Seq<u32>, slot: u32)
    requires
        free_wf(n1, head, f),
        !f.contains(slot),
        n1.len() == n2.len(),
        forall|s: int| 0 <= s < n1.len() && s != slot && !n1[s].live ==> #[trigger] n2[s] == n1[s],
    ensures free_wf(n2, head, f),
{
    assert forall|i: int| 0 <= i < f.len() implies {
        &&& ((#[trigger] f[i]) as int) < n2.len()
        &&& !n2[f[i] as int].live
        &&& n2[f[i] as int].next == next_of(f, i)
    } by {
        assert(f[i] != slot);
        assert(!n1[f[i] as int].live);
    }
}

proof fn lemma_partition_after_push(n1: Seq<Node>, n2: Seq<Node>, e1: Engine, e2: Engine, side: Side, ticks: u32, slot: u32, t: u32)
    requires
        side_partition(n1, e1.bids, Side::Buy, ticks),
        side_partition(n1, e1.asks, Side::Sell, ticks),
        n1.len() == n2.len(),
        (slot as int) < n1.len(),
        n2[slot as int].live,
        n2[slot as int].side == side,
        idx(ticks, side, n2[slot as int].price) == t,
        t < ticks,
        lad_of(e2, side).lists@ == lad_of(e1, side).lists@.update(t as int, lad_of(e1, side).lists@[t as int].push(slot)),
        lad_of(e1, side).lists@.len() == ticks,
        lad_of(e2, opp(side)) == lad_of(e1, opp(side)),
        frame(n1, n2, side, slot as int),
        forall|s: int| 0 <= s < n1.len() && s != slot ==> (#[trigger] n2[s]).live == n1[s].live && n2[s].side == n1[s].side && n2[s].price == n1[s].price,
    ensures
        side_partition(n2, e2.bids, Side::Buy, ticks),
        side_partition(n2, e2.asks, Side::Sell, ticks),
{
    assert forall|sd: Side| #![auto] side_partition(n2, lad_of(e2, sd), sd, ticks) by {
        assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == sd
            implies in_lad(n2, lad_of(e2, sd), sd, ticks, s) by {
            if s == slot {
                let l2 = lad_of(e2, side).lists@[t as int];
                assert(l2[l2.len() - 1] == slot);
            } else {
                assert(n1[s].live);
                if sd == side {
                    assert(in_lad(n1, lad_of(e1, sd), sd, ticks, s));
                    let tt = idx(ticks, sd, n1[s].price);
                    let l = lad_of(e1, sd).lists@[tt];
                    let k = choose|k: int| 0 <= k < l.len() && l[k] == s as u32;
                    if tt == t { assert(l.push(slot)[k] == s as u32); }
                } else {
                    assert(n2[s] == n1[s]);
                    assert(in_lad(n1, lad_of(e1, sd), sd, ticks, s));
                }
            }
        }
    }
    assert(side_partition(n2, lad_of(e2, Side::Buy), Side::Buy, ticks));
    assert(side_partition(n2, lad_of(e2, Side::Sell), Side::Sell, ticks));
}

proof fn lemma_lookup_none(e: Engine, id: u64)
    requires e.wf(),
    ensures
        (slot_of(id) >= e.cap
            || !e.nodes@[slot_of(id)].live
            || e.nodes@[slot_of(id)].id != id) ==> find(e.view(), id) is None,
{
    let s = e.view();
    if slot_of(id) >= e.cap || !e.nodes@[slot_of(id)].live || e.nodes@[slot_of(id)].id != id {
        assert forall|sd: Side| !has_id(#[trigger] book(s, sd), id) by {
            if has_id(book(s, sd), id) {
                let lad = lad_of(e, sd);
                let k = choose|k: int| 0 <= k < book(s, sd).len() && book(s, sd)[k].id == id;
                let L = ladder_view(e.nodes@, lad.lists@);
                assert(book(s, sd) == flat(L));
                let (tt, j) = lemma_flat_member(L, k);
                lemma_ladder_indexed(e.nodes@, lad, sd, e.ticks);
                lemma_member(e.nodes@, lad, sd, e.ticks, tt, j);
                let x = lad.lists@[tt][j];
                assert(L[tt][j] == ord(e.nodes@[x as int]));
                assert(slot_of(id) == x as int);
            }
        }
        assert(!has_id(book(s, Side::Buy), id));
        assert(!has_id(book(s, Side::Sell), id));
    }
}

proof fn lemma_lookup_some(e: Engine, id: u64, slot: u32)
    requires
        e.wf(),
        (slot as int) < e.nodes@.len(),
        e.nodes@[slot as int].live,
        e.nodes@[slot as int].id == id,
    ensures ({
        let n = e.nodes@[slot as int];
        let t = idx(e.ticks, n.side, n.price);
        let lad = lad_of(e, n.side);
        &&& lad.lists@[t].contains(slot)
        &&& find(e.view(), id) == Some((n.side, flat_pos(ladder_view(e.nodes@, lad.lists@), t, lad.lists@[t].index_of(slot))))
    }),
{
    let s = e.view();
    let n = e.nodes@[slot as int];
    let sd = n.side;
    let lad = lad_of(e, sd);
    let t = idx(e.ticks, sd, n.price);
    assert(in_lad(e.nodes@, lad, sd, e.ticks, slot as int));
    let l = lad.lists@[t];
    l.index_of_first_ensures(slot);
    let i = l.index_of(slot);
    let L = ladder_view(e.nodes@, lad.lists@);
    lemma_ladder_indexed(e.nodes@, lad, sd, e.ticks);
    lemma_flat_pos(L, t, i);
    let j = flat_pos(L, t, i);
    assert(book(s, sd)[j].id == id);
    assert(has_id(book(s, sd), id));
    // ids are unique, so the model's choice is this position
    let pj = pos_of(book(s, sd), id);
    assert(book(s, sd)[pj].id == id);
    if sd is Sell {
        if has_id(s.bids, id) {
            let k = choose|k: int| 0 <= k < s.bids.len() && s.bids[k].id == id;
            assert(s.bids[k].id != s.asks[j].id);
        }
    }
}


// ---------------------------------------------------------------------------
// Snapshots: export the abstract state, and rebuild an engine from one.
//
// Together with `theorem_replay_compose` these make snapshot-based recovery
// exact: restoring the exported state after command prefix `a` and replaying
// suffix `b` yields the same state and events as replaying `a + b`.

/// Ordered by priority with strictly increasing keys (adjacent check suffices).
pub open spec fn adj_sorted(ticks: u32, side: Side, b: Seq<SOrder>) -> bool {
    forall|k: int| 0 < k < b.len() ==> #[trigger] key_lt(ticks, side, b[k - 1], b[k])
}

proof fn lemma_key_lt_trans(ticks: u32, side: Side, a: SOrder, b: SOrder, c: SOrder)
    requires key_lt(ticks, side, a, b), key_lt(ticks, side, b, c),
    ensures key_lt(ticks, side, a, c),
{
}

proof fn lemma_adj_sorted(ticks: u32, side: Side, b: Seq<SOrder>)
    requires adj_sorted(ticks, side, b),
    ensures sorted(ticks, side, b),
{
    assert forall|i: int, j: int| 0 <= i < j < b.len() implies #[trigger] key_lt(ticks, side, b[i], b[j]) by {
        lemma_adj_sorted_from(ticks, side, b, i, j);
    }
}

proof fn lemma_adj_sorted_from(ticks: u32, side: Side, b: Seq<SOrder>, i: int, j: int)
    requires adj_sorted(ticks, side, b), 0 <= i < j < b.len(),
    ensures key_lt(ticks, side, b[i], b[j]),
    decreases j - i,
{
    assert(key_lt(ticks, side, b[j - 1], b[j]));
    if i < j - 1 {
        lemma_adj_sorted_from(ticks, side, b, i, j - 1);
        lemma_key_lt_trans(ticks, side, b[i], b[j - 1], b[j]);
    }
}

fn key_lt_exec(ticks: u32, side: Side, a: SOrder, b: SOrder) -> (r: bool)
    requires a.price < ticks, b.price < ticks,
    ensures r == key_lt(ticks, side, a, b),
{
    let ia = level_index(ticks, side, a.price);
    let ib = level_index(ticks, side, b.price);
    ia < ib || (ia == ib && a.id / SLOT_SPACE < b.id / SLOT_SPACE)
}

/// Push every order of one ladder, best level first, FIFO within a level.
fn export_side(nodes: &Vec<Node>, lad: &Ladder, side: Side, ticks: u32, out: &mut Vec<SOrder>)
    requires ladder_wf(nodes@, *lad, side, ticks),
    ensures out@ == old(out)@ + side_view(nodes@, *lad),
{
    let ghost L = ladder_view(nodes@, lad.lists@);
    let ghost out0 = out@;
    proof {
        lemma_ladder_indexed(nodes@, *lad, side, ticks);
        lemma_flat_take_empty(L, lad.best as int);
        assert(out0 + flat(L.take(lad.best as int)) =~= out0);
    }
    let mut t = lad.best;
    while t < ticks
        invariant
            ladder_wf(nodes@, *lad, side, ticks),
            L == ladder_view(nodes@, lad.lists@),
            L.len() == ticks,
            t <= ticks,
            out@ == out0 + flat(L.take(t as int)),
        decreases ticks - t,
    {
        let ghost l = lad.lists@[t as int];
        let mut cur = lad.levels[t as usize].head;
        let ghost mut i: int = 0;
        proof {
            assert(level_wf(nodes@, lad.levels@[t as int], l, side, t as int, ticks));
            assert(L[t as int].take(0) =~= Seq::<SOrder>::empty());
            assert(out@ =~= out0 + flat(L.take(t as int)) + L[t as int].take(0));
        }
        while cur != NIL
            invariant
                ladder_wf(nodes@, *lad, side, ticks),
                L == ladder_view(nodes@, lad.lists@),
                t < ticks,
                l == lad.lists@[t as int],
                level_wf(nodes@, lad.levels@[t as int], l, side, t as int, ticks),
                0 <= i <= l.len(),
                cur == (if i < l.len() { l[i] } else { NIL }),
                out@ == out0 + flat(L.take(t as int)) + L[t as int].take(i),
            decreases l.len() - i,
        {
            proof { assert(member_ok(nodes@, l, i, side, t as int, ticks)); }
            let n = nodes[cur as usize];
            out.push(SOrder { id: n.id, price: n.price, qty: n.qty });
            proof {
                assert(L[t as int][i] == ord(nodes@[l[i] as int]));
                assert(L[t as int].take(i + 1) =~= L[t as int].take(i).push(L[t as int][i]));
                i = i + 1;
            }
            cur = n.next;
        }
        proof {
            assert(L[t as int].take(i) =~= L[t as int]);
            lemma_flat_len_take(L, t as int);
            assert(out@ =~= out0 + flat(L.take(t as int + 1)));
        }
        t = t + 1;
    }
    proof { assert(L.take(ticks as int) =~= L); }
}

/// An empty engine shell: every node dead, nothing free, nothing listed.
fn blank(ticks: u32, cap: u32) -> (e: Engine)
    requires 1 <= ticks <= MAX_TICKS, 1 <= cap <= MAX_CAPACITY,
    ensures
        e.ticks == ticks, e.cap == cap, e.next_seq == 0,
        e.nodes@.len() == cap,
        forall|s: int| 0 <= s < cap ==> !(#[trigger] e.nodes@[s]).live,
        e.free@ == Seq::<u32>::empty(), e.free_head == NIL,
        ladder_wf(e.nodes@, e.bids, Side::Buy, ticks),
        ladder_wf(e.nodes@, e.asks, Side::Sell, ticks),
        forall|t: int| 0 <= t < ticks ==> (#[trigger] e.bids.lists@[t]).len() == 0,
        forall|t: int| 0 <= t < ticks ==> (#[trigger] e.asks.lists@[t]).len() == 0,
{
    let mut nodes: Vec<Node> = Vec::with_capacity(cap as usize);
    let mut i: u32 = 0;
    while i < cap
        invariant i <= cap, nodes@.len() == i, forall|k: int| 0 <= k < i ==> !(#[trigger] nodes@[k]).live,
        decreases cap - i,
    {
        nodes.push(Node { id: 0, qty: 0, next: NIL, prev: NIL, price: 0, side: Side::Buy, live: false });
        i = i + 1;
    }
    let mut bl: Vec<Level> = Vec::with_capacity(ticks as usize);
    let mut al: Vec<Level> = Vec::with_capacity(ticks as usize);
    let mut t: u32 = 0;
    while t < ticks
        invariant
            t <= ticks, bl@.len() == t, al@.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] bl@[k]) == (Level { head: NIL, tail: NIL }),
            forall|k: int| 0 <= k < t ==> (#[trigger] al@[k]) == (Level { head: NIL, tail: NIL }),
        decreases ticks - t,
    {
        bl.push(Level { head: NIL, tail: NIL });
        al.push(Level { head: NIL, tail: NIL });
        t = t + 1;
    }
    let ghost empty_lists: Seq<Seq<u32>> = Seq::new(ticks as nat, |k: int| Seq::<u32>::empty());
    let e = Engine {
        ticks,
        cap,
        nodes,
        free_head: NIL,
        free: Ghost(Seq::empty()),
        bids: Ladder { levels: bl, best: ticks, lists: Ghost(empty_lists) },
        asks: Ladder { levels: al, best: ticks, lists: Ghost(empty_lists) },
        next_seq: 0,
    };
    proof {
        assert forall|tt: int| 0 <= tt < ticks implies #[trigger] level_wf(e.nodes@, e.bids.levels@[tt], e.bids.lists@[tt], Side::Buy, tt, ticks) by {}
        assert forall|tt: int| 0 <= tt < ticks implies #[trigger] level_wf(e.nodes@, e.asks.levels@[tt], e.asks.lists@[tt], Side::Sell, tt, ticks) by {}
    }
    e
}

/// Inserting an order whose index is not better than anything already on the
/// side appends it.
proof fn lemma_ins_pos_end(ticks: u32, side: Side, bk: Seq<SOrder>, i: int)
    requires forall|k: int| 0 <= k < bk.len() ==> idx(ticks, side, (#[trigger] bk[k]).price) <= i,
    ensures ins_pos(ticks, side, bk, i) == bk.len(),
    decreases bk.len(),
{
    if bk.len() > 0 {
        assert forall|k: int| 0 <= k < bk.drop_first().len() implies idx(ticks, side, (#[trigger] bk.drop_first()[k]).price) <= i by {
            assert(bk.drop_first()[k] == bk[k + 1]);
        }
        lemma_ins_pos_end(ticks, side, bk.drop_first(), i);
    }
}

impl Engine {
    /// Export the abstract state (both sides in priority order, the free
    /// stack, and the next sequence number).
    pub fn export(&self, bids: &mut Vec<SOrder>, asks: &mut Vec<SOrder>, free: &mut Vec<u32>) -> (next_seq: u64)
        requires self.wf(),
        ensures
            bids@ == old(bids)@ + self.view().bids,
            asks@ == old(asks)@ + self.view().asks,
            free@ == old(free)@ + self.view().free,
            next_seq == self.view().next_seq,
            self.view().ticks == self.ticks,
    {
        export_side(&self.nodes, &self.bids, Side::Buy, self.ticks, bids);
        export_side(&self.nodes, &self.asks, Side::Sell, self.ticks, asks);
        let ghost f = self.free@;
        let ghost free0 = free@;
        let mut cur = self.free_head;
        let ghost mut i: int = 0;
        proof { assert(free0 + f.take(0) =~= free0); }
        while cur != NIL
            invariant
                free_wf(self.nodes@, self.free_head, f),
                f == self.free@,
                0 <= i <= f.len(),
                cur == (if i < f.len() { f[i] } else { NIL }),
                free@ == free0 + f.take(i),
            decreases f.len() - i,
        {
            free.push(cur);
            proof {
                assert(f.take(i + 1) =~= f.take(i).push(f[i]));
            }
            cur = self.nodes[cur as usize].next;
            proof { i = i + 1; }
        }
        proof { assert(f.take(i) =~= f); }
        self.next_seq
    }

    /// Rebuild an engine from an exported state, after checking at run time
    /// that it satisfies the model invariant. Returns `None` for any state
    /// that is not a valid engine state for this configuration.
    pub fn import(ticks: u32, cap: u32, bids: &Vec<SOrder>, asks: &Vec<SOrder>, free: &Vec<u32>, next_seq: u64) -> (r: Option<Engine>)
        ensures
            r matches Some(e) ==> e.wf() && e.view() == (SState { ticks, bids: bids@, asks: asks@, free: free@, next_seq }),
    {
        if !(1 <= ticks && ticks <= MAX_TICKS && 1 <= cap && cap <= MAX_CAPACITY && next_seq <= MAX_SEQ + 1) {
            return None;
        }
        if !check_side(ticks, cap, Side::Buy, bids, next_seq) || !check_side(ticks, cap, Side::Sell, asks, next_seq) {
            return None;
        }
        if bids.len() > 0 && asks.len() > 0 && bids[0].price >= asks[0].price {
            return None;
        }
        // every slot used at most once across orders and the free stack
        let mut used: Vec<bool> = Vec::with_capacity(cap as usize);
        let mut k: u32 = 0;
        while k < cap
            invariant k <= cap, used@.len() == k, forall|j: int| 0 <= j < k ==> !(#[trigger] used@[j]),
            decreases cap - k,
        {
            used.push(false);
            k = k + 1;
        }
        if !mark_side(&mut used, bids, cap) {
            return None;
        }
        let ghost used_b = used@;
        if !mark_side(&mut used, asks, cap) {
            return None;
        }
        let ghost used_ba = used@;
        let mut j: usize = 0;
        while j < free.len()
            invariant
                used@.len() == cap,
                0 <= j <= free@.len(),
                forall|a: int| 0 <= a < j ==> (#[trigger] free@[a]) < cap && used@[free@[a] as int],
                forall|a: int, b: int| 0 <= a < b < j ==> free@[a] != free@[b],
                forall|a: int| 0 <= a < j ==> !used_ba[(#[trigger] free@[a]) as int],
                forall|x: int| 0 <= x < cap && used_ba[x] ==> #[trigger] used@[x],
            decreases free@.len() - j,
        {
            let x = free[j];
            if x >= cap || used[x as usize] {
                return None;
            }
            used[x as usize] = true;
            proof {
                assert forall|a: int, b: int| 0 <= a < b < j + 1 implies free@[a] != free@[b] by {
                    if b == j { assert(used@[free@[a] as int]); }
                }
            }
            j = j + 1;
        }
        let mut e = blank(ticks, cap);
        e.next_seq = next_seq;
        e.fill_side(Side::Buy, bids);
        e.fill_side(Side::Sell, asks);
        e.fill_free(free);
        proof {
            let v = e.view();
            lemma_adj_sorted(ticks, Side::Buy, bids@);
            lemma_adj_sorted(ticks, Side::Sell, asks@);
            assert(inv(v));
        }
        Some(e)
    }
}


fn check_side(ticks: u32, cap: u32, side: Side, b: &Vec<SOrder>, next_seq: u64) -> (r: bool)
    requires 1 <= ticks, cap <= MAX_CAPACITY,
    ensures
        r ==> adj_sorted(ticks, side, b@),
        r ==> orders_ok(ticks, next_seq, b@),
        r ==> forall|k: int| 0 <= k < b@.len() ==> slot_of((#[trigger] b@[k]).id) < cap,
{
    let mut k: usize = 0;
    while k < b.len()
        invariant
            1 <= ticks,
            k <= b@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] order_ok(ticks, next_seq, b@[j]),
            forall|j: int| 0 <= j < k ==> slot_of((#[trigger] b@[j]).id) < cap,
            forall|j: int| 0 < j < k ==> #[trigger] key_lt(ticks, side, b@[j - 1], b@[j]),
        decreases b@.len() - k,
    {
        let o = b[k];
        if o.price >= ticks || o.qty == 0 || o.qty > MAX_QTY || o.id / SLOT_SPACE >= next_seq || o.id % SLOT_SPACE >= cap as u64 {
            return false;
        }
        if k > 0 && !key_lt_exec(ticks, side, b[k - 1], o) {
            return false;
        }
        k = k + 1;
    }
    true
}

/// Mark the slot of every order; fail if any slot is out of range or reused.
fn mark_side(used: &mut Vec<bool>, b: &Vec<SOrder>, cap: u32) -> (r: bool)
    requires
        old(used)@.len() == cap,
        forall|k: int| 0 <= k < b@.len() ==> slot_of((#[trigger] b@[k]).id) < cap,
    ensures
        used@.len() == cap,
        forall|x: int| 0 <= x < cap && old(used)@[x] ==> #[trigger] used@[x],
        r ==> forall|k: int| 0 <= k < b@.len() ==> #[trigger] used@[slot_of(b@[k].id)],
        r ==> forall|k: int| 0 <= k < b@.len() ==> !old(used)@[slot_of((#[trigger] b@[k]).id)],
        r ==> forall|k1: int, k2: int| 0 <= k1 < k2 < b@.len() ==> slot_of(b@[k1].id) != slot_of(b@[k2].id),
{
    let mut k: usize = 0;
    while k < b.len()
        invariant
            used@.len() == cap,
            k <= b@.len(),
            forall|j: int| 0 <= j < b@.len() ==> slot_of((#[trigger] b@[j]).id) < cap,
            forall|x: int| 0 <= x < cap && old(used)@[x] ==> #[trigger] used@[x],
            forall|j: int| 0 <= j < k ==> #[trigger] used@[slot_of(b@[j].id)],
            forall|j: int| 0 <= j < k ==> !old(used)@[slot_of((#[trigger] b@[j]).id)],
            forall|j1: int, j2: int| 0 <= j1 < j2 < k ==> slot_of(b@[j1].id) != slot_of(b@[j2].id),
            forall|x: int| 0 <= x < cap && used@[x] && !old(used)@[x] ==> exists|j: int| 0 <= j < k && slot_of(#[trigger] b@[j].id) == x,
        decreases b@.len() - k,
    {
        let x = (b[k].id % SLOT_SPACE) as usize;
        if used[x] {
            return false;
        }
        proof {
            assert(!old(used)@[x as int]);
            assert forall|j: int| 0 <= j < k implies slot_of(b@[j].id) != x as int by {
                assert(used@[slot_of(b@[j].id)]);
            }
        }
        used[x] = true;
        k = k + 1;
    }
    true
}

impl Engine {
    /// Append the orders of `b` (already validated) to one empty side.
    fn fill_side(&mut self, side: Side, b: &Vec<SOrder>)
        requires
            old(self).nodes@.len() == old(self).cap,
            1 <= old(self).ticks,
            ladder_wf(old(self).nodes@, old(self).bids, Side::Buy, old(self).ticks),
            ladder_wf(old(self).nodes@, old(self).asks, Side::Sell, old(self).ticks),
            forall|t: int| 0 <= t < old(self).ticks ==> (#[trigger] lad_of(*old(self), side).lists@[t]).len() == 0,
            side_partition(old(self).nodes@, old(self).bids, Side::Buy, old(self).ticks),
            side_partition(old(self).nodes@, old(self).asks, Side::Sell, old(self).ticks),
            adj_sorted(old(self).ticks, side, b@),
            orders_ok(old(self).ticks, old(self).next_seq, b@),
            forall|k: int| 0 <= k < b@.len() ==> slot_of((#[trigger] b@[k]).id) < old(self).cap,
            forall|k: int| 0 <= k < b@.len() ==> !old(self).nodes@[slot_of((#[trigger] b@[k]).id)].live,
            forall|k1: int, k2: int| 0 <= k1 < k2 < b@.len() ==> slot_of(b@[k1].id) != slot_of(b@[k2].id),
        ensures
            self.ticks == old(self).ticks, self.cap == old(self).cap, self.next_seq == old(self).next_seq,
            self.free == old(self).free, self.free_head == old(self).free_head,
            self.nodes@.len() == old(self).nodes@.len(),
            ladder_wf(self.nodes@, self.bids, Side::Buy, self.ticks),
            ladder_wf(self.nodes@, self.asks, Side::Sell, self.ticks),
            side_partition(self.nodes@, self.bids, Side::Buy, self.ticks),
            side_partition(self.nodes@, self.asks, Side::Sell, self.ticks),
            side_view(self.nodes@, lad_of(*self, side)) == b@,
            side_view(self.nodes@, lad_of(*self, opp(side))) == side_view(old(self).nodes@, lad_of(*old(self), opp(side))),
            forall|s: int| 0 <= s < self.nodes@.len() && !(exists|k: int| 0 <= k < b@.len() && slot_of(#[trigger] b@[k].id) == s)
                ==> #[trigger] self.nodes@[s] == old(self).nodes@[s],
    {
        let ticks = self.ticks;
        let ghost n0 = self.nodes@;
        proof {
            let L = ladder_view(n0, lad_of(*self, side).lists@);
            lemma_ladder_indexed(n0, lad_of(*self, side), side, ticks);
            assert forall|t: int| 0 <= t < L.len() implies (#[trigger] L[t]).len() == 0 by {}
            lemma_flat_all_empty(L);
            assert(b@.take(0) =~= Seq::<SOrder>::empty());
            lemma_adj_sorted(ticks, side, b@);
        }
        let mut k: usize = 0;
        while k < b.len()
            invariant
                self.ticks == ticks, 1 <= ticks,
                self.cap == old(self).cap, self.next_seq == old(self).next_seq,
                self.free == old(self).free, self.free_head == old(self).free_head,
                self.nodes@.len() == n0.len(),
                k <= b@.len(),
                ladder_wf(self.nodes@, self.bids, Side::Buy, ticks),
                ladder_wf(self.nodes@, self.asks, Side::Sell, ticks),
                side_partition(self.nodes@, self.bids, Side::Buy, ticks),
                side_partition(self.nodes@, self.asks, Side::Sell, ticks),
                lad_of(*self, opp(side)) == lad_of(*old(self), opp(side)),
                side_view(self.nodes@, lad_of(*self, side)) == b@.take(k as int),
                sorted(ticks, side, b@),
                orders_ok(ticks, old(self).next_seq, b@),
                forall|j: int| 0 <= j < b@.len() ==> slot_of((#[trigger] b@[j]).id) < old(self).cap,
                forall|j: int| k <= j < b@.len() ==> !self.nodes@[slot_of((#[trigger] b@[j]).id)].live,
                forall|j1: int, j2: int| 0 <= j1 < j2 < b@.len() ==> slot_of(b@[j1].id) != slot_of(b@[j2].id),
                forall|s: int| 0 <= s < n0.len() && !(exists|j: int| 0 <= j < k && slot_of(#[trigger] b@[j].id) == s)
                    ==> #[trigger] self.nodes@[s] == n0[s],
                forall|s: int| 0 <= s < n0.len() && self.nodes@[s].live && self.nodes@[s].side == opp(side) ==> #[trigger] self.nodes@[s] == n0[s],
            decreases b@.len() - k,
        {
            let o = b[k];
            let slot = (o.id % SLOT_SPACE) as u32;
            let t = level_index(ticks, side, o.price);
            proof { assert(order_ok(ticks, old(self).next_seq, b@[k as int])); }
            let ghost n1 = self.nodes@;
            let ghost lad1 = lad_of(*self, side);
            if is_buy(side) {
                push_back(&mut self.nodes, &mut self.bids, side, ticks, t, slot, o.id, o.price, o.qty);
                proof { lemma_ladder_frame(n1, self.nodes@, self.asks, Side::Sell, ticks); }
            } else {
                push_back(&mut self.nodes, &mut self.asks, side, ticks, t, slot, o.id, o.price, o.qty);
                proof { lemma_ladder_frame(n1, self.nodes@, self.bids, Side::Buy, ticks); }
            }
            proof {
                let n2 = self.nodes@;
                let L = ladder_view(n1, lad1.lists@);
                lemma_ladder_indexed(n1, lad1, side, ticks);
                lemma_flat_push_level(ticks, side, L, t as int, o);
                let cur = b@.take(k as int);
                assert forall|j: int| 0 <= j < cur.len() implies idx(ticks, side, (#[trigger] cur[j]).price) <= t as int by {
                    assert(key_lt(ticks, side, b@[j], b@[k as int]));
                }
                lemma_ins_pos_end(ticks, side, cur, t as int);
                assert(b@.take(k as int + 1) =~= cur.insert(cur.len() as int, o));
                // partitions
                lemma_partition_after_push_raw(n1, n2, lad1, lad_of(*self, side), lad_of(*self, opp(side)), side, ticks, slot, t);
                assert forall|j: int| k + 1 <= j < b@.len() implies !n2[slot_of((#[trigger] b@[j]).id)].live by {
                    assert(slot_of(b@[j].id) != slot as int);
                }
                assert forall|s: int| 0 <= s < n0.len() && !(exists|j: int| 0 <= j < k + 1 && slot_of(#[trigger] b@[j].id) == s)
                    implies #[trigger] n2[s] == n0[s] by {
                    assert(slot_of(b@[k as int].id) == slot as int);
                    if s == slot as int { assert(false); }
                    if !(n1[s].live && n1[s].side == side) {
                        assert(n2[s] == n1[s]);
                    } else {
                        // live nodes of `side` are all orders already pushed
                        lemma_live_side_pushed(n0, n1, *old(self), side, b@, k as int, s);
                    }
                }
                assert forall|s: int| 0 <= s < n0.len() && n2[s].live && n2[s].side == opp(side) implies #[trigger] n2[s] == n0[s] by {
                    if s != slot as int {
                        assert(n2[s] == n1[s]);
                    }
                }
            }
            k = k + 1;
        }
        proof { assert(b@.take(b@.len() as int) =~= b@); }
    }

    /// Build the free stack so that its top is `f[0]`.
    fn fill_free(&mut self, f: &Vec<u32>)
        requires
            old(self).nodes@.len() == old(self).cap,
            old(self).free@ == Seq::<u32>::empty(),
            old(self).free_head == NIL,
            forall|a: int| 0 <= a < f@.len() ==> (#[trigger] f@[a]) < old(self).cap && !old(self).nodes@[f@[a] as int].live,
            forall|a: int, b: int| 0 <= a < b < f@.len() ==> f@[a] != f@[b],
        ensures
            self.free@ == f@,
            free_wf(self.nodes@, self.free_head, self.free@),
            self.nodes@.len() == old(self).nodes@.len(),
            forall|s: int| 0 <= s < self.nodes@.len() ==> payload_same(#[trigger] self.nodes@[s], old(self).nodes@[s])
                && self.nodes@[s].live == old(self).nodes@[s].live && self.nodes@[s].prev == old(self).nodes@[s].prev,
            forall|s: int| 0 <= s < self.nodes@.len() && old(self).nodes@[s].live ==> #[trigger] self.nodes@[s] == old(self).nodes@[s],
            self.ticks == old(self).ticks, self.cap == old(self).cap, self.next_seq == old(self).next_seq,
            self.bids == old(self).bids, self.asks == old(self).asks,
    {
        let mut j = f.len();
        proof { assert(f@.skip(j as int) =~= Seq::<u32>::empty()); }
        while j > 0
            invariant
                j <= f@.len(),
                self.nodes@.len() == old(self).nodes@.len(),
                self.free@ == f@.skip(j as int),
                free_wf(self.nodes@, self.free_head, self.free@),
                forall|a: int| 0 <= a < f@.len() ==> (#[trigger] f@[a]) < old(self).cap && !old(self).nodes@[f@[a] as int].live,
                forall|a: int, b: int| 0 <= a < b < f@.len() ==> f@[a] != f@[b],
                forall|s: int| 0 <= s < self.nodes@.len() ==> payload_same(#[trigger] self.nodes@[s], old(self).nodes@[s])
                    && self.nodes@[s].live == old(self).nodes@[s].live && self.nodes@[s].prev == old(self).nodes@[s].prev,
                forall|s: int| 0 <= s < self.nodes@.len() && old(self).nodes@[s].live ==> #[trigger] self.nodes@[s] == old(self).nodes@[s],
                self.ticks == old(self).ticks, self.cap == old(self).cap, self.next_seq == old(self).next_seq,
                self.bids == old(self).bids, self.asks == old(self).asks,
            decreases j,
        {
            j = j - 1;
            let x = f[j];
            proof {
                if self.free@.contains(x) {
                    let k = choose|k: int| 0 <= k < self.free@.len() && self.free@[k] == x;
                    assert(f@[j as int + 1 + k] == x);
                }
            }
            let g = free_push(&mut self.nodes, &mut self.free_head, Ghost(self.free@), x);
            self.free = g;
            proof { assert(self.free@ =~= f@.skip(j as int)); }
        }
    }
}

proof fn lemma_partition_after_push_raw(n1: Seq<Node>, n2: Seq<Node>, lad1: Ladder, lad2: Ladder, other: Ladder, side: Side, ticks: u32, slot: u32, t: u32)
    requires
        side_partition(n1, lad1, side, ticks),
        side_partition(n1, other, opp(side), ticks),
        n1.len() == n2.len(),
        (slot as int) < n1.len(),
        n2[slot as int].live,
        n2[slot as int].side == side,
        idx(ticks, side, n2[slot as int].price) == t,
        t < ticks,
        lad1.lists@.len() == ticks,
        lad2.lists@ == lad1.lists@.update(t as int, lad1.lists@[t as int].push(slot)),
        frame(n1, n2, side, slot as int),
        forall|s: int| 0 <= s < n1.len() && s != slot ==> (#[trigger] n2[s]).live == n1[s].live && n2[s].side == n1[s].side && n2[s].price == n1[s].price,
    ensures
        side_partition(n2, lad2, side, ticks),
        side_partition(n2, other, opp(side), ticks),
{
    assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == side
        implies in_lad(n2, lad2, side, ticks, s) by {
        if s == slot {
            let l2 = lad2.lists@[t as int];
            assert(l2[l2.len() - 1] == slot);
        } else {
            assert(in_lad(n1, lad1, side, ticks, s));
            let tt = idx(ticks, side, n1[s].price);
            let l = lad1.lists@[tt];
            let k = choose|k: int| 0 <= k < l.len() && l[k] == s as u32;
            if tt == t { assert(l.push(slot)[k] == s as u32); }
        }
    }
    assert forall|s: int| 0 <= s < n2.len() && (#[trigger] n2[s]).live && n2[s].side == opp(side)
        implies in_lad(n2, other, opp(side), ticks, s) by {
        assert(s != slot);
        assert(n2[s] == n1[s]);
        assert(in_lad(n1, other, opp(side), ticks, s));
    }
}

/// While filling one side, its live nodes are exactly the slots pushed so far.
proof fn lemma_live_side_pushed(n0: Seq<Node>, n1: Seq<Node>, e0: Engine, side: Side, b: Seq<SOrder>, k: int, s: int)
    requires
        0 <= s < n0.len(),
        n1.len() == n0.len(),
        forall|t: int| 0 <= t < e0.ticks ==> (#[trigger] lad_of(e0, side).lists@[t]).len() == 0,
        side_partition(n0, lad_of(e0, side), side, e0.ticks),
        n1[s].live, n1[s].side == side,
        forall|x: int| 0 <= x < n0.len() && !(exists|j: int| 0 <= j < k && slot_of(#[trigger] b[j].id) == x) ==> #[trigger] n1[x] == n0[x],
    ensures exists|j: int| 0 <= j < k && slot_of(#[trigger] b[j].id) == s,
{
    if !(exists|j: int| 0 <= j < k && slot_of(#[trigger] b[j].id) == s) {
        assert(n1[s] == n0[s]);
        assert(in_lad(n0, lad_of(e0, side), side, e0.ticks, s));
    }
}

} // verus!


