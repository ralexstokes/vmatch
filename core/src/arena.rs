//! Preallocated arena of order nodes, threaded into intrusive doubly linked
//! FIFO lists (one per price level per side) and a singly linked free stack.
//! Every operation is O(1) and allocation-free.

use crate::{bitmap::*, flat::*, spec::*, types::*};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug)]
pub struct Node {
    pub id: u64,
    pub qty: u64,
    pub next: u32,
    pub prev: u32,
    pub price: u32,
    pub side: Side,
    pub live: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct Level {
    pub head: u32,
    pub tail: u32,
}

/// One side of the book: a level per priority index plus the best index.
pub struct Ladder {
    pub levels: Vec<Level>,
    /// Index of the best non-empty level, or `ticks` if the side is empty.
    pub best: u32,
    /// Ghost: the slots in each level, front (oldest) first.
    pub lists: Ghost<Seq<Seq<u32>>>,
    /// Which levels are non-empty, for finding the next best level in O(1).
    pub bits: Bitmap,
}

// ---------------------------------------------------------------------------
// Abstraction.

pub open spec fn ord(n: Node) -> SOrder {
    SOrder { id: n.id, price: n.price, qty: n.qty }
}

pub open spec fn level_view(nodes: Seq<Node>, l: Seq<u32>) -> Seq<SOrder> {
    Seq::new(l.len(), |i: int| ord(nodes[l[i] as int]))
}

pub open spec fn ladder_view(nodes: Seq<Node>, ls: Seq<Seq<u32>>) -> Seq<Seq<SOrder>> {
    Seq::new(ls.len(), |t: int| level_view(nodes, ls[t]))
}

pub open spec fn side_view(nodes: Seq<Node>, lad: Ladder) -> Seq<SOrder> {
    flat(ladder_view(nodes, lad.lists@))
}

// ---------------------------------------------------------------------------
// Well-formedness.

pub open spec fn next_of(l: Seq<u32>, i: int) -> u32 {
    if i + 1 < l.len() { l[i + 1] } else { NIL }
}

pub open spec fn prev_of(l: Seq<u32>, i: int) -> u32 {
    if i > 0 { l[i - 1] } else { NIL }
}

pub open spec fn member_ok(nodes: Seq<Node>, l: Seq<u32>, i: int, side: Side, t: int, ticks: u32) -> bool {
    let s = l[i];
    let n = nodes[s as int];
    &&& (s as int) < nodes.len()
    &&& n.next == next_of(l, i)
    &&& n.prev == prev_of(l, i)
    &&& n.live
    &&& n.side == side
    &&& idx(ticks, side, n.price) == t
    &&& valid_qty(n.qty)
    &&& slot_of(n.id) == s as int
}

pub open spec fn level_wf(nodes: Seq<Node>, lv: Level, l: Seq<u32>, side: Side, t: int, ticks: u32) -> bool {
    &&& l.no_duplicates()
    &&& (l.len() == 0 ==> lv.head == NIL && lv.tail == NIL)
    &&& (l.len() > 0 ==> lv.head == l[0] && lv.tail == l[l.len() - 1])
    &&& forall|i: int| 0 <= i < l.len() ==> #[trigger] member_ok(nodes, l, i, side, t, ticks)
}

pub open spec fn best_ok(lad: Ladder, ticks: u32) -> bool {
    &&& lad.best <= ticks
    &&& forall|t: int| 0 <= t < lad.best ==> (#[trigger] lad.lists@[t]).len() == 0
    &&& lad.best < ticks ==> lad.lists@[lad.best as int].len() > 0
}

/// Which levels of a ladder are non-empty.
pub open spec fn nonempty(ls: Seq<Seq<u32>>) -> Seq<bool> {
    Seq::new(ls.len(), |t: int| ls[t].len() > 0)
}

pub open spec fn ladder_wf(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32) -> bool {
    &&& nodes.len() <= MAX_CAPACITY
    &&& ticks <= MAX_TICKS
    &&& bitmap_wf(lad.bits, nonempty(lad.lists@))
    &&& lad.levels@.len() == ticks
    &&& lad.lists@.len() == ticks
    &&& forall|t: int| 0 <= t < ticks ==> #[trigger] level_wf(nodes, lad.levels@[t], lad.lists@[t], side, t, ticks)
    &&& best_ok(lad, ticks)
}

pub open spec fn free_wf(nodes: Seq<Node>, head: u32, f: Seq<u32>) -> bool {
    &&& nodes.len() <= MAX_CAPACITY
    &&& f.no_duplicates()
    &&& (f.len() == 0 ==> head == NIL)
    &&& (f.len() > 0 ==> head == f[0])
    &&& forall|i: int| 0 <= i < f.len() ==> {
        &&& ((#[trigger] f[i]) as int) < nodes.len()
        &&& !nodes[f[i] as int].live
        &&& nodes[f[i] as int].next == next_of(f, i)
    }
}

pub open spec fn payload_same(a: Node, b: Node) -> bool {
    a.id == b.id && a.qty == b.qty && a.price == b.price && a.side == b.side
}

/// Nodes outside `side`'s live set are untouched.
pub open spec fn frame(old: Seq<Node>, new: Seq<Node>, side: Side, extra: int) -> bool {
    &&& new.len() == old.len()
    &&& forall|s: int| 0 <= s < old.len() && s != extra && !(old[s].live && old[s].side == side)
        ==> #[trigger] new[s] == old[s]
}

// ---------------------------------------------------------------------------
// Basic lemmas.

pub proof fn lemma_level_view_index(nodes: Seq<Node>, l: Seq<u32>, i: int)
    requires 0 <= i < l.len(),
    ensures level_view(nodes, l)[i] == ord(nodes[l[i] as int]), level_view(nodes, l).len() == l.len(),
{
}

/// A level only depends on the nodes of its members.
pub proof fn lemma_level_frame(n1: Seq<Node>, n2: Seq<Node>, lv: Level, l: Seq<u32>, side: Side, t: int, ticks: u32)
    requires
        level_wf(n1, lv, l, side, t, ticks),
        n1.len() == n2.len(),
        forall|i: int| 0 <= i < l.len() ==> n2[(#[trigger] l[i]) as int] == n1[l[i] as int],
    ensures
        level_wf(n2, lv, l, side, t, ticks),
        level_view(n2, l) =~= level_view(n1, l),
{
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] member_ok(n2, l, i, side, t, ticks) by {
        assert(member_ok(n1, l, i, side, t, ticks));
        assert(n2[l[i] as int] == n1[l[i] as int]);
    }
}

/// Members of a well-formed ladder are live nodes of that side whose index is
/// their level.
pub proof fn lemma_member(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32, t: int, i: int)
    requires ladder_wf(nodes, lad, side, ticks), 0 <= t < ticks, 0 <= i < lad.lists@[t].len(),
    ensures
        level_wf(nodes, lad.levels@[t], lad.lists@[t], side, t, ticks),
        member_ok(nodes, lad.lists@[t], i, side, t, ticks),
        nodes[lad.lists@[t][i] as int].live,
        nodes[lad.lists@[t][i] as int].side == side,
        idx(ticks, side, nodes[lad.lists@[t][i] as int].price) == t,
{
    assert(level_wf(nodes, lad.levels@[t], lad.lists@[t], side, t, ticks));
    assert(member_ok(nodes, lad.lists@[t], i, side, t, ticks));
}

/// A ladder is unaffected by changes to nodes that are not its members.
pub proof fn lemma_ladder_frame(n1: Seq<Node>, n2: Seq<Node>, lad: Ladder, side: Side, ticks: u32)
    requires
        ladder_wf(n1, lad, side, ticks),
        n1.len() == n2.len(),
        forall|s: int| 0 <= s < n1.len() && n1[s].live && n1[s].side == side ==> #[trigger] n2[s] == n1[s],
    ensures
        ladder_wf(n2, lad, side, ticks),
        ladder_view(n2, lad.lists@) =~= ladder_view(n1, lad.lists@),
{
    assert forall|t: int| 0 <= t < ticks implies #[trigger] level_wf(n2, lad.levels@[t], lad.lists@[t], side, t, ticks)
        && level_view(n2, lad.lists@[t]) =~= level_view(n1, lad.lists@[t]) by {
        let l = lad.lists@[t];
        assert forall|i: int| 0 <= i < l.len() implies n2[(#[trigger] l[i]) as int] == n1[l[i] as int] by {
            lemma_member(n1, lad, side, ticks, t, i);
        }
        lemma_level_frame(n1, n2, lad.levels@[t], l, side, t, ticks);
    }
    assert forall|t: int| 0 <= t < lad.lists@.len() implies
        ladder_view(n2, lad.lists@)[t] =~= ladder_view(n1, lad.lists@)[t] by {
        assert(level_wf(n2, lad.levels@[t], lad.lists@[t], side, t, ticks));
    }
}

pub proof fn lemma_free_frame(n1: Seq<Node>, n2: Seq<Node>, head: u32, f: Seq<u32>)
    requires
        free_wf(n1, head, f),
        n1.len() == n2.len(),
        forall|s: int| 0 <= s < n1.len() && !n1[s].live ==> #[trigger] n2[s] == n1[s],
    ensures free_wf(n2, head, f),
{
    assert forall|i: int| 0 <= i < f.len() implies {
        &&& ((#[trigger] f[i]) as int) < n2.len()
        &&& !n2[f[i] as int].live
        &&& n2[f[i] as int].next == next_of(f, i)
    } by {
        assert(!n1[f[i] as int].live);
    }
}

/// The view of a ladder is indexed: level `t` only holds orders at index `t`.
pub proof fn lemma_ladder_indexed(nodes: Seq<Node>, lad: Ladder, side: Side, ticks: u32)
    requires ladder_wf(nodes, lad, side, ticks),
    ensures
        levels_indexed(ticks, side, ladder_view(nodes, lad.lists@), 0),
        ladder_view(nodes, lad.lists@).len() == ticks,
        forall|t: int| 0 <= t < ticks ==> (#[trigger] ladder_view(nodes, lad.lists@)[t]).len() == lad.lists@[t].len(),
{
    let L = ladder_view(nodes, lad.lists@);
    assert forall|t: int, j: int| 0 <= t < L.len() && 0 <= j < L[t].len()
        implies idx(ticks, side, (#[trigger] L[t][j]).price) == 0 + t by {
        lemma_member(nodes, lad, side, ticks, t, j);
    }
}

// ---------------------------------------------------------------------------
// Operations.

pub fn level_index(ticks: u32, side: Side, price: u32) -> (r: u32)
    requires price < ticks,
    ensures r as int == idx(ticks, side, price), r < ticks,
{
    match side {
        Side::Buy => ticks - 1 - price,
        Side::Sell => price,
    }
}

/// Append a node at the tail of level `t`, writing its payload.
pub fn push_back(
    nodes: &mut Vec<Node>,
    lad: &mut Ladder,
    side: Side,
    ticks: u32,
    t: u32,
    slot: u32,
    id: u64,
    price: u32,
    qty: u64,
)
    requires
        ladder_wf(old(nodes)@, *old(lad), side, ticks),
        (slot as int) < old(nodes)@.len(),
        !old(nodes)@[slot as int].live,
        t < ticks,
        price < ticks,
        idx(ticks, side, price) == t,
        valid_qty(qty),
        slot_of(id) == slot,
    ensures
        ladder_wf(final(nodes)@, *final(lad), side, ticks),
        final(lad).lists@ == old(lad).lists@.update(t as int, old(lad).lists@[t as int].push(slot)),
        frame(old(nodes)@, final(nodes)@, side, slot as int),
        final(nodes)@[slot as int].live,
        final(nodes)@[slot as int].side == side,
        ord(final(nodes)@[slot as int]) == (SOrder { id, price, qty }),
        forall|s: int| 0 <= s < final(nodes)@.len() && s != slot ==>
            payload_same(#[trigger] final(nodes)@[s], old(nodes)@[s]) && final(nodes)@[s].live == old(nodes)@[s].live,
        ladder_view(final(nodes)@, final(lad).lists@) =~= ladder_view(old(nodes)@, old(lad).lists@).update(
            t as int,
            ladder_view(old(nodes)@, old(lad).lists@)[t as int].push(SOrder { id, price, qty }),
        ),
{
    let ghost n0 = nodes@;
    let ghost ls0 = lad.lists@;
    let ghost lad0 = *lad;
    let ghost l0 = ls0[t as int];
    proof {
        assert(level_wf(n0, lad.levels@[t as int], l0, side, t as int, ticks));
        // the new slot is not a member of any level (members are live)
        assert forall|tt: int, i: int| 0 <= tt < ticks && 0 <= i < ls0[tt].len() implies ls0[tt][i] != slot by {
            lemma_member(n0, *lad, side, ticks, tt, i);
        }
    }
    let lv = lad.levels[t as usize];
    let old_tail = lv.tail;
    nodes[slot as usize] = Node { id, qty, next: NIL, prev: old_tail, price, side, live: true };
    if old_tail == NIL {
        proof {
            if l0.len() > 0 { lemma_member(n0, lad0, side, ticks, t as int, l0.len() - 1); }
        }
        lad.levels[t as usize] = Level { head: slot, tail: slot };
    } else {
        proof { lemma_member(n0, *lad, side, ticks, t as int, l0.len() - 1); }
        let mut tn = nodes[old_tail as usize];
        tn.next = slot;
        nodes[old_tail as usize] = tn;
        lad.levels[t as usize] = Level { head: lv.head, tail: slot };
    }
    let ghost l1 = l0.push(slot);
    proof {
        lad.lists@ = ls0.update(t as int, l1);
    }
    lad.bits.set(Ghost(nonempty(ls0)), t);
    proof { assert(nonempty(lad.lists@) =~= nonempty(ls0).update(t as int, true)); }
    if t < lad.best {
        lad.best = t;
    }
    proof {
        let n1 = nodes@;
        // level t
        assert(l1.no_duplicates());
        assert forall|i: int| 0 <= i < l1.len() implies #[trigger] member_ok(n1, l1, i, side, t as int, ticks) by {
            if i < l0.len() {
                assert(member_ok(n0, l0, i, side, t as int, ticks));
                assert(l1[i] == l0[i]);
                if i + 1 < l0.len() {
                    assert(l1[i] != old_tail || i == l0.len() - 1) by {
                        if l1[i] == old_tail { assert(l0[i] == l0[l0.len() - 1]); }
                    }
                }
            }
        }
        // other levels: their members are neither `slot` nor `old_tail`
        assert forall|tt: int| 0 <= tt < ticks && tt != t implies
            #[trigger] level_wf(n1, lad.levels@[tt], lad.lists@[tt], side, tt, ticks)
            && level_view(n1, lad.lists@[tt]) =~= level_view(n0, ls0[tt]) by {
            let l = ls0[tt];
            assert forall|i: int| 0 <= i < l.len() implies n1[(#[trigger] l[i]) as int] == n0[l[i] as int] by {
                lemma_member(n0, lad0, side, ticks, tt, i);
                if l0.len() > 0 {
                    lemma_member(n0, lad0, side, ticks, t as int, l0.len() - 1);
                }
            }
            assert(level_wf(n0, lad0.levels@[tt], l, side, tt, ticks));
            lemma_level_frame(n0, n1, lad.levels@[tt], l, side, tt, ticks);
        }
        assert(level_wf(n1, lad.levels@[t as int], lad.lists@[t as int], side, t as int, ticks));
        // frame
        assert forall|s: int| 0 <= s < n0.len() && s != slot && !(n0[s].live && n0[s].side == side)
            implies #[trigger] n1[s] == n0[s] by {
            if l0.len() > 0 {
                lemma_member(n0, lad0, side, ticks, t as int, l0.len() - 1);
            }
        }
        // view
        let V0 = ladder_view(n0, ls0);
        let V1 = ladder_view(n1, lad.lists@);
        assert forall|tt: int| 0 <= tt < ticks implies V1[tt] =~= V0.update(t as int, V0[t as int].push(SOrder { id, price, qty }))[tt] by {
            if tt == t {
                assert forall|i: int| 0 <= i < l1.len() implies level_view(n1, l1)[i] == V0[t as int].push(SOrder { id, price, qty })[i] by {
                    if i < l0.len() {
                        if l0[i] == old_tail { assert(i == l0.len() - 1); }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_remove_no_duplicates(l: Seq<u32>, i: int)
    requires l.no_duplicates(), 0 <= i < l.len(),
    ensures l.remove(i).no_duplicates(),
{
    let l1 = l.remove(i);
    assert forall|a: int, b: int| 0 <= a < l1.len() && 0 <= b < l1.len() && a != b implies l1[a] != l1[b] by {
        let aa = if a < i { a } else { a + 1 };
        let bb = if b < i { b } else { b + 1 };
        assert(l1[a] == l[aa] && l1[b] == l[bb]);
    }
}

/// Unlinking position `i` of a well-formed level: the slot is marked dead and
/// its neighbours are linked to each other.
proof fn lemma_unlink_level(
    n0: Seq<Node>,
    n1: Seq<Node>,
    lv0: Level,
    lv1: Level,
    l0: Seq<u32>,
    i: int,
    side: Side,
    t: int,
    ticks: u32,
)
    requires
        level_wf(n0, lv0, l0, side, t, ticks),
        n0.len() <= MAX_CAPACITY,
        n1.len() == n0.len(),
        0 <= i < l0.len(),
        forall|s: int| 0 <= s < n0.len() && s != l0[i] && s != prev_of(l0, i) && s != next_of(l0, i)
            ==> #[trigger] n1[s] == n0[s],
        n1[l0[i] as int] == (Node { live: false, ..n0[l0[i] as int] }),
        i > 0 ==> n1[l0[i - 1] as int] == (Node { next: next_of(l0, i), ..n0[l0[i - 1] as int] }),
        i + 1 < l0.len() ==> n1[l0[i + 1] as int] == (Node { prev: prev_of(l0, i), ..n0[l0[i + 1] as int] }),
        lv1.head == (if i == 0 { next_of(l0, i) } else { lv0.head }),
        lv1.tail == (if i + 1 == l0.len() { prev_of(l0, i) } else { lv0.tail }),
    ensures
        level_wf(n1, lv1, l0.remove(i), side, t, ticks),
        level_view(n1, l0.remove(i)) =~= level_view(n0, l0).remove(i),
{
    // Distinctness is only needed at a few specific pairs; reveal it there.
    hide(Seq::no_duplicates);
    let l1 = l0.remove(i);
    lemma_remove_no_duplicates(l0, i);
    assert forall|j: int| 0 <= j < l1.len() implies #[trigger] member_ok(n1, l1, j, side, t, ticks)
        && n1[l1[j] as int].id == n0[l1[j] as int].id
        && n1[l1[j] as int].price == n0[l1[j] as int].price
        && n1[l1[j] as int].qty == n0[l1[j] as int].qty by {
        let jj = if j < i { j } else { j + 1 };
        assert(l1[j] == l0[jj]);
        assert(member_ok(n0, l0, jj, side, t, ticks));
        assert(l0[jj] != l0[i]) by { reveal(Seq::no_duplicates); }
        if i > 0 && jj != i - 1 { assert(l0[jj] != l0[i - 1]) by { reveal(Seq::no_duplicates); } }
        if i + 1 < l0.len() && jj != i + 1 { assert(l0[jj] != l0[i + 1]) by { reveal(Seq::no_duplicates); } }
        if i > 0 { assert(member_ok(n0, l0, i - 1, side, t, ticks)); }
        if i + 1 < l0.len() { assert(member_ok(n0, l0, i + 1, side, t, ticks)); }
        if jj + 1 < l0.len() { assert(member_ok(n0, l0, jj + 1, side, t, ticks)); }
        if jj > 0 { assert(member_ok(n0, l0, jj - 1, side, t, ticks)); }
    }
    if l1.len() > 0 {
        assert(member_ok(n0, l0, 0, side, t, ticks));
        assert(member_ok(n0, l0, l0.len() - 1, side, t, ticks));
    }
    assert forall|j: int| 0 <= j < l1.len() implies level_view(n1, l1)[j] == level_view(n0, l0).remove(i)[j] by {
        assert(member_ok(n1, l1, j, side, t, ticks));
    }
}

/// Remove the member at position `i` of level `t` (O(1) via the prev/next
/// links), mark it dead and repair `best` if its level became empty.
pub fn unlink(nodes: &mut Vec<Node>, lad: &mut Ladder, side: Side, ticks: u32, t: u32, slot: u32, Ghost(i): Ghost<int>)
    requires
        ladder_wf(old(nodes)@, *old(lad), side, ticks),
        t < ticks,
        0 <= i < old(lad).lists@[t as int].len(),
        old(lad).lists@[t as int][i] == slot,
    ensures
        ladder_wf(final(nodes)@, *final(lad), side, ticks),
        final(lad).lists@ == old(lad).lists@.update(t as int, old(lad).lists@[t as int].remove(i)),
        frame(old(nodes)@, final(nodes)@, side, -1),
        !final(nodes)@[slot as int].live,
        ord(final(nodes)@[slot as int]) == ord(old(nodes)@[slot as int]),
        final(nodes)@[slot as int].side == old(nodes)@[slot as int].side,
        final(nodes)@[slot as int].price == old(nodes)@[slot as int].price,
        forall|s: int| 0 <= s < final(nodes)@.len() && s != slot ==> #[trigger] final(nodes)@[s].live == old(nodes)@[s].live,
        forall|s: int| 0 <= s < final(nodes)@.len() ==> payload_same(#[trigger] final(nodes)@[s], old(nodes)@[s]),
        final(nodes)@.len() == old(nodes)@.len(),
        ladder_view(final(nodes)@, final(lad).lists@) =~= ladder_view(old(nodes)@, old(lad).lists@).update(
            t as int,
            ladder_view(old(nodes)@, old(lad).lists@)[t as int].remove(i),
        ),
{
    let ghost n0 = nodes@;
    let ghost ls0 = lad.lists@;
    let ghost lad0 = *lad;
    let ghost l0 = ls0[t as int];
    proof {
        lemma_member(n0, lad0, side, ticks, t as int, i);
        if i > 0 { lemma_member(n0, lad0, side, ticks, t as int, i - 1); }
        if i + 1 < l0.len() { lemma_member(n0, lad0, side, ticks, t as int, i + 1); }
    }
    let n = nodes[slot as usize];
    let p = n.prev;
    let nx = n.next;
    let lv = lad.levels[t as usize];
    let mut head = lv.head;
    let mut tail = lv.tail;
    if p == NIL {
        head = nx;
    } else {
        let mut pn = nodes[p as usize];
        pn.next = nx;
        nodes[p as usize] = pn;
    }
    if nx == NIL {
        tail = p;
    } else {
        let mut nn = nodes[nx as usize];
        nn.prev = p;
        nodes[nx as usize] = nn;
    }
    lad.levels[t as usize] = Level { head, tail };
    let mut dead = n;
    dead.live = false;
    nodes[slot as usize] = dead;
    let ghost l1 = l0.remove(i);
    proof {
        lad.lists@ = ls0.update(t as int, l1);
        let n1 = nodes@;
        assert(n1.len() == n0.len());
        assert(p == prev_of(l0, i) && nx == next_of(l0, i));
        assert(p == NIL <==> i == 0);
        assert(nx == NIL <==> i + 1 == l0.len());
        assert forall|s: int| 0 <= s < n0.len() && s != l0[i] && s != prev_of(l0, i) && s != next_of(l0, i)
            implies #[trigger] n1[s] == n0[s] by {}
        lemma_unlink_level(n0, n1, lad0.levels@[t as int], lad.levels@[t as int], l0, i, side, t as int, ticks);
        // other levels: their members are at other indices, so none of them is
        // `slot` or one of its neighbours
        assert forall|tt: int| 0 <= tt < ticks && tt != t implies
            #[trigger] level_wf(n1, lad.levels@[tt], lad.lists@[tt], side, tt, ticks)
            && level_view(n1, lad.lists@[tt]) =~= level_view(n0, ls0[tt]) by {
            let l = ls0[tt];
            assert forall|k: int| 0 <= k < l.len() implies n1[(#[trigger] l[k]) as int] == n0[l[k] as int] by {
                lemma_member(n0, lad0, side, ticks, tt, k);
            }
            lemma_level_frame(n0, n1, lad.levels@[tt], l, side, tt, ticks);
        }
        assert forall|s: int| 0 <= s < n0.len() && s != -1 && !(n0[s].live && n0[s].side == side)
            implies #[trigger] n1[s] == n0[s] by {}
        let V0 = ladder_view(n0, ls0);
        let V1 = ladder_view(n1, lad.lists@);
        assert forall|tt: int| 0 <= tt < ticks implies V1[tt] =~= V0.update(t as int, V0[t as int].remove(i))[tt] by {
            if tt != t {
                assert(level_wf(n1, lad.levels@[tt], lad.lists@[tt], side, tt, ticks));
            }
        }
    }
    // repair best
    let emptied = head == NIL;
    proof {
        assert(level_wf(nodes@, lad.levels@[t as int], l1, side, t as int, ticks));
        if l1.len() > 0 { assert(head == l1[0]); assert(member_ok(nodes@, l1, 0, side, t as int, ticks)); }
        assert(emptied <==> l1.len() == 0);
    }
    if emptied {
        lad.bits.clear(Ghost(nonempty(ls0)), t);
        proof { assert(nonempty(lad.lists@) =~= nonempty(ls0).update(t as int, false)); }
        if lad.best == t {
            let b = lad.bits.next(Ghost(nonempty(lad.lists@)), ticks, t + 1);
            proof {
                assert forall|tt: int| t + 1 <= tt < b implies (#[trigger] lad.lists@[tt]).len() == 0 by {
                    assert(!nonempty(lad.lists@)[tt]);
                }
                if b < ticks { assert(nonempty(lad.lists@)[b as int]); }
            }
            lad.best = b;
        }
    } else {
        proof { assert(nonempty(lad.lists@) =~= nonempty(ls0)); }
    }
}

/// Overwrite the quantity of the member at position `i` of level `t`.
pub fn set_qty(nodes: &mut Vec<Node>, lad: &Ladder, side: Side, ticks: u32, t: u32, slot: u32, Ghost(i): Ghost<int>, qty: u64)
    requires
        ladder_wf(old(nodes)@, *lad, side, ticks),
        t < ticks,
        0 <= i < lad.lists@[t as int].len(),
        lad.lists@[t as int][i] == slot,
        valid_qty(qty),
    ensures
        ladder_wf(final(nodes)@, *lad, side, ticks),
        frame(old(nodes)@, final(nodes)@, side, -1),
        forall|s: int| 0 <= s < final(nodes)@.len() ==> #[trigger] final(nodes)@[s].live == old(nodes)@[s].live,
        forall|s: int| 0 <= s < final(nodes)@.len() ==> #[trigger] final(nodes)@[s].side == old(nodes)@[s].side,
        forall|s: int| 0 <= s < final(nodes)@.len() ==> #[trigger] final(nodes)@[s].price == old(nodes)@[s].price,
        forall|s: int| 0 <= s < final(nodes)@.len() && s != slot ==> #[trigger] final(nodes)@[s] == old(nodes)@[s],
        final(nodes)@.len() == old(nodes)@.len(),
        final(nodes)@[slot as int] == (Node { qty, ..old(nodes)@[slot as int] }),
        ladder_view(final(nodes)@, lad.lists@) =~= ladder_view(old(nodes)@, lad.lists@).update(
            t as int,
            ladder_view(old(nodes)@, lad.lists@)[t as int].update(i, SOrder { qty, ..ladder_view(old(nodes)@, lad.lists@)[t as int][i] }),
        ),
{
    let ghost n0 = nodes@;
    proof {
        lemma_member(n0, *lad, side, ticks, t as int, i);
        assert(level_wf(n0, lad.levels@[t as int], lad.lists@[t as int], side, t as int, ticks));
    }
    let mut n = nodes[slot as usize];
    n.qty = qty;
    nodes[slot as usize] = n;
    proof {
        let n1 = nodes@;
        let ls = lad.lists@;
        let l0 = ls[t as int];
        assert forall|j: int| 0 <= j < l0.len() implies #[trigger] member_ok(n1, l0, j, side, t as int, ticks) by {
            assert(member_ok(n0, l0, j, side, t as int, ticks));
        }
        assert(level_wf(n1, lad.levels@[t as int], l0, side, t as int, ticks));
        assert forall|tt: int| 0 <= tt < ticks && tt != t implies
            #[trigger] level_wf(n1, lad.levels@[tt], ls[tt], side, tt, ticks)
            && level_view(n1, ls[tt]) =~= level_view(n0, ls[tt]) by {
            let l = ls[tt];
            assert forall|k: int| 0 <= k < l.len() implies n1[(#[trigger] l[k]) as int] == n0[l[k] as int] by {
                lemma_member(n0, *lad, side, ticks, tt, k);
            }
            assert(level_wf(n0, lad.levels@[tt], l, side, tt, ticks));
            lemma_level_frame(n0, n1, lad.levels@[tt], l, side, tt, ticks);
        }
        let V0 = ladder_view(n0, ls);
        let V1 = ladder_view(n1, ls);
        assert forall|tt: int| 0 <= tt < ticks implies
            V1[tt] =~= V0.update(t as int, V0[t as int].update(i, SOrder { qty, ..V0[t as int][i] }))[tt] by {
            if tt == t {
                assert forall|j: int| 0 <= j < l0.len() implies level_view(n1, l0)[j]
                    == V0[t as int].update(i, SOrder { qty, ..V0[t as int][i] })[j] by {
                    if j != i { assert(l0[j] != slot); }
                }
            } else {
                assert(level_wf(n1, lad.levels@[tt], ls[tt], side, tt, ticks));
            }
        }
    }
}

/// Push a dead, unlisted slot onto the free stack.
pub fn free_push(nodes: &mut Vec<Node>, head: &mut u32, Ghost(f): Ghost<Seq<u32>>, slot: u32) -> (r: Ghost<Seq<u32>>)
    requires
        free_wf(old(nodes)@, *old(head), f),
        (slot as int) < old(nodes)@.len(),
        !old(nodes)@[slot as int].live,
        !f.contains(slot),
    ensures
        r@ == seq![slot] + f,
        free_wf(final(nodes)@, *final(head), r@),
        final(nodes)@.len() == old(nodes)@.len(),
        forall|s: int| 0 <= s < final(nodes)@.len() && s != slot ==> #[trigger] final(nodes)@[s] == old(nodes)@[s],
        final(nodes)@[slot as int] == (Node { next: *old(head), ..old(nodes)@[slot as int] }),
{
    let mut n = nodes[slot as usize];
    n.next = *head;
    nodes[slot as usize] = n;
    *head = slot;
    let ghost f2 = seq![slot] + f;
    proof {
        assert forall|i: int| 0 <= i < f2.len() implies {
            &&& ((#[trigger] f2[i]) as int) < nodes@.len()
            &&& !nodes@[f2[i] as int].live
            &&& nodes@[f2[i] as int].next == next_of(f2, i)
        } by {
            if i > 0 {
                assert(f2[i] == f[i - 1]);
                assert(f[i - 1] != slot);
            }
        }
        assert forall|a: int, b: int| 0 <= a < f2.len() && 0 <= b < f2.len() && a != b implies f2[a] != f2[b] by {
            if a > 0 && b > 0 { assert(f2[a] == f[a - 1] && f2[b] == f[b - 1]); }
            else if a == 0 { assert(f2[b] == f[b - 1]); }
            else { assert(f2[a] == f[a - 1]); }
        }
    }
    Ghost(f2)
}

/// Pop the top of the free stack.
pub fn free_pop(nodes: &Vec<Node>, head: &mut u32, Ghost(f): Ghost<Seq<u32>>) -> (r: (u32, Ghost<Seq<u32>>))
    requires
        free_wf(nodes@, *old(head), f),
        f.len() > 0,
    ensures
        r.0 == f[0],
        r.1@ == f.drop_first(),
        free_wf(nodes@, *final(head), r.1@),
        (r.0 as int) < nodes@.len(),
        !nodes@[r.0 as int].live,
        !r.1@.contains(r.0),
{
    let slot = *head;
    proof { assert(f[0] == slot); }
    *head = nodes[slot as usize].next;
    let ghost f2 = f.drop_first();
    proof {
        assert forall|i: int| 0 <= i < f2.len() implies {
            &&& ((#[trigger] f2[i]) as int) < nodes@.len()
            &&& !nodes@[f2[i] as int].live
            &&& nodes@[f2[i] as int].next == next_of(f2, i)
        } by {
            assert(f2[i] == f[i + 1]);
        }
        assert(f2.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < f2.len() && 0 <= b < f2.len() && a != b implies f2[a] != f2[b] by {
                assert(f2[a] == f[a + 1] && f2[b] == f[b + 1]);
            }
        }
        assert(*head == next_of(f, 0));
        if f2.len() > 0 { assert(f2[0] == f[1]); }
        if f2.contains(slot) {
            let k = choose|k: int| 0 <= k < f2.len() && f2[k] == slot;
            assert(f[k + 1] == f[0]);
        }
    }
    (slot, Ghost(f2))
}

} // verus!
