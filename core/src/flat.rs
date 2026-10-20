//! Lemmas relating a ladder of FIFO price levels (`Seq<Seq<SOrder>>`, indexed
//! by priority index) to the single priority-ordered sequence of the model.

use vstd::prelude::*;
use crate::types::*;
use crate::spec::*;
use crate::props::*;

verus! {

/// Concatenate levels in index order (best level first).
pub open spec fn flat(L: Seq<Seq<SOrder>>) -> Seq<SOrder>
    decreases L.len(),
{
    if L.len() == 0 { Seq::empty() } else { L[0] + flat(L.drop_first()) }
}

pub proof fn lemma_flat_add(a: Seq<Seq<SOrder>>, b: Seq<Seq<SOrder>>)
    ensures flat(a + b) =~= flat(a) + flat(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_flat_add(a.drop_first(), b);
    }
}

pub proof fn lemma_flat_one(x: Seq<SOrder>)
    ensures flat(seq![x]) =~= x,
{
    reveal_with_fuel(flat, 2);
    assert(seq![x].drop_first() =~= Seq::<Seq<SOrder>>::empty());
}

/// `flat(L) == flat(L[..t]) + L[t] + flat(L[t+1..])`
pub proof fn lemma_flat_split(L: Seq<Seq<SOrder>>, t: int)
    requires 0 <= t < L.len(),
    ensures flat(L) =~= flat(L.take(t)) + L[t] + flat(L.skip(t + 1)),
{
    assert(L =~= L.take(t) + (seq![L[t]] + L.skip(t + 1)));
    lemma_flat_add(L.take(t), seq![L[t]] + L.skip(t + 1));
    lemma_flat_add(seq![L[t]], L.skip(t + 1));
    lemma_flat_one(L[t]);
}

pub proof fn lemma_flat_take_skip(L: Seq<Seq<SOrder>>, t: int)
    requires 0 <= t <= L.len(),
    ensures flat(L) =~= flat(L.take(t)) + flat(L.skip(t)),
{
    assert(L =~= L.take(t) + L.skip(t));
    lemma_flat_add(L.take(t), L.skip(t));
}

pub proof fn lemma_flat_all_empty(L: Seq<Seq<SOrder>>)
    requires forall|i: int| 0 <= i < L.len() ==> (#[trigger] L[i]).len() == 0,
    ensures flat(L) =~= Seq::<SOrder>::empty(),
    decreases L.len(),
{
    if L.len() > 0 {
        assert forall|i: int| 0 <= i < L.drop_first().len() implies (#[trigger] L.drop_first()[i]).len() == 0 by {
            assert(L.drop_first()[i] == L[i + 1]);
        }
        lemma_flat_all_empty(L.drop_first());
    }
}

/// Replacing one level replaces the corresponding slice of the flat sequence.
pub proof fn lemma_flat_update(L: Seq<Seq<SOrder>>, t: int, x: Seq<SOrder>)
    requires 0 <= t < L.len(),
    ensures
        flat(L.update(t, x)) =~= flat(L.take(t)) + x + flat(L.skip(t + 1)),
        flat(L) =~= flat(L.take(t)) + L[t] + flat(L.skip(t + 1)),
{
    let L2 = L.update(t, x);
    lemma_flat_split(L, t);
    lemma_flat_split(L2, t);
    assert(L2.take(t) =~= L.take(t));
    assert(L2.skip(t + 1) =~= L.skip(t + 1));
}

/// Every order in level `t` has priority index `base + t`.
pub open spec fn levels_indexed(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, base: int) -> bool {
    forall|t: int, j: int| 0 <= t < L.len() && 0 <= j < L[t].len() ==> idx(ticks, side, (#[trigger] L[t][j]).price) == base + t
}

pub proof fn lemma_levels_indexed_skip(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, base: int, n: int)
    requires levels_indexed(ticks, side, L, base), 0 <= n <= L.len(),
    ensures levels_indexed(ticks, side, L.skip(n), base + n),
{
    assert forall|t: int, j: int| 0 <= t < L.skip(n).len() && 0 <= j < L.skip(n)[t].len()
        implies idx(ticks, side, (#[trigger] L.skip(n)[t][j]).price) == base + n + t by {
        assert(L.skip(n)[t] == L[t + n]);
        assert(idx(ticks, side, L[t + n][j].price) == base + t + n);
    }
}

pub proof fn lemma_levels_indexed_take(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, base: int, n: int)
    requires levels_indexed(ticks, side, L, base), 0 <= n <= L.len(),
    ensures levels_indexed(ticks, side, L.take(n), base),
{
    assert forall|t: int, j: int| 0 <= t < L.take(n).len() && 0 <= j < L.take(n)[t].len()
        implies idx(ticks, side, (#[trigger] L.take(n)[t][j]).price) == base + t by {
        assert(L.take(n)[t] == L[t]);
        assert(idx(ticks, side, L[t][j].price) == base + t);
    }
}

/// Every element of `flat(L)` has an index in `[base, base + L.len())`.
pub proof fn lemma_flat_idx_range(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, base: int)
    requires levels_indexed(ticks, side, L, base),
    ensures forall|k: int| 0 <= k < flat(L).len() ==>
        base <= idx(ticks, side, (#[trigger] flat(L)[k]).price) < base + L.len(),
    decreases L.len(),
{
    if L.len() > 0 {
        let t = L.drop_first();
        assert(t =~= L.skip(1));
        lemma_levels_indexed_skip(ticks, side, L, base, 1);
        lemma_flat_idx_range(ticks, side, t, base + 1);
        assert forall|k: int| 0 <= k < flat(L).len()
            implies base <= idx(ticks, side, (#[trigger] flat(L)[k]).price) < base + L.len() by {
            if k < L[0].len() {
                assert(flat(L)[k] == L[0][k]);
                assert(idx(ticks, side, L[0][k].price) == base + 0);
            } else {
                assert(flat(L)[k] == flat(t)[k - L[0].len()]);
            }
        }
    }
}

pub proof fn lemma_ins_pos_concat(ticks: u32, side: Side, a: Seq<SOrder>, b: Seq<SOrder>, i: int)
    requires forall|k: int| 0 <= k < a.len() ==> idx(ticks, side, (#[trigger] a[k]).price) <= i,
    ensures ins_pos(ticks, side, a + b, i) == a.len() + ins_pos(ticks, side, b, i),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert forall|k: int| 0 <= k < a.drop_first().len() implies idx(ticks, side, (#[trigger] a.drop_first()[k]).price) <= i by {
            assert(a.drop_first()[k] == a[k + 1]);
        }
        lemma_ins_pos_concat(ticks, side, a.drop_first(), b, i);
    }
}

/// The model's insertion position for a new order at level `i` is right after
/// everything in levels `0..=i`, i.e. at the tail of level `i`.
pub proof fn lemma_ins_pos_flat(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, i: int)
    requires levels_indexed(ticks, side, L, 0), 0 <= i < L.len(),
    ensures ins_pos(ticks, side, flat(L), i) == flat(L.take(i + 1)).len(),
{
    let a = flat(L.take(i + 1));
    let b = flat(L.skip(i + 1));
    lemma_flat_take_skip(L, i + 1);
    lemma_levels_indexed_take(ticks, side, L, 0, i + 1);
    lemma_flat_idx_range(ticks, side, L.take(i + 1), 0);
    lemma_levels_indexed_skip(ticks, side, L, 0, i + 1);
    lemma_flat_idx_range(ticks, side, L.skip(i + 1), i + 1);
    lemma_ins_pos_concat(ticks, side, a, b, i);
    if b.len() > 0 {
        assert(idx(ticks, side, b[0].price) >= i + 1);
    }
}

/// Inserting at the tail of level `i` is inserting at `ins_pos` in the flat view.
pub proof fn lemma_flat_push_level(ticks: u32, side: Side, L: Seq<Seq<SOrder>>, i: int, o: SOrder)
    requires levels_indexed(ticks, side, L, 0), 0 <= i < L.len(),
    ensures flat(L.update(i, L[i].push(o))) =~= flat(L).insert(ins_pos(ticks, side, flat(L), i), o),
{
    lemma_ins_pos_flat(ticks, side, L, i);
    lemma_flat_update(L, i, L[i].push(o));
    lemma_flat_split(L.take(i + 1), i);
    assert(L.take(i + 1).take(i) =~= L.take(i));
    assert(L.take(i + 1).skip(i + 1) =~= Seq::<Seq<SOrder>>::empty());
    assert(L.take(i + 1)[i] == L[i]);
}

/// With all levels before `b` empty, the flat view starts with level `b`.
pub proof fn lemma_flat_best(L: Seq<Seq<SOrder>>, b: int)
    requires
        0 <= b < L.len(),
        forall|t: int| 0 <= t < b ==> (#[trigger] L[t]).len() == 0,
    ensures
        flat(L) =~= L[b] + flat(L.skip(b + 1)),
{
    lemma_flat_split(L, b);
    assert forall|t: int| 0 <= t < L.take(b).len() implies (#[trigger] L.take(b)[t]).len() == 0 by {
        assert(L.take(b)[t] == L[t]);
    }
    lemma_flat_all_empty(L.take(b));
}

/// Total quantity over a flat view is the sum over levels.
pub proof fn lemma_flat_len_take(L: Seq<Seq<SOrder>>, t: int)
    requires 0 <= t < L.len(),
    ensures flat(L.take(t + 1)) =~= flat(L.take(t)) + L[t],
{
    assert(L.take(t + 1) =~= L.take(t) + seq![L[t]]);
    lemma_flat_add(L.take(t), seq![L[t]]);
    lemma_flat_one(L[t]);
}

/// `fillable` over a flat view: levels `0..=lim` all cross, later ones don't.
pub proof fn lemma_fillable_concat(ticks: u32, ms: Side, a: Seq<SOrder>, b: Seq<SOrder>, lim: int)
    requires forall|k: int| 0 <= k < a.len() ==> #[trigger] crosses(ticks, ms, a[k], lim),
    ensures fillable(ticks, ms, a + b, lim) == qsum(a) + fillable(ticks, ms, b, lim),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert forall|k: int| 0 <= k < a.drop_first().len() implies #[trigger] crosses(ticks, ms, a.drop_first()[k], lim) by {
            assert(a.drop_first()[k] == a[k + 1]);
            assert(crosses(ticks, ms, a[k + 1], lim));
        }
        lemma_fillable_concat(ticks, ms, a.drop_first(), b, lim);
    }
}

pub proof fn lemma_fillable_flat(ticks: u32, ms: Side, L: Seq<Seq<SOrder>>, lim: int)
    requires levels_indexed(ticks, ms, L, 0), 0 <= lim,
    ensures fillable(ticks, ms, flat(L), lim) == qsum(flat(L.take(if lim + 1 < L.len() { lim + 1 } else { L.len() as int }))),
{
    let n = if lim + 1 < L.len() { lim + 1 } else { L.len() as int };
    let a = flat(L.take(n));
    let b = flat(L.skip(n));
    lemma_flat_take_skip(L, n);
    lemma_levels_indexed_take(ticks, ms, L, 0, n);
    lemma_flat_idx_range(ticks, ms, L.take(n), 0);
    lemma_levels_indexed_skip(ticks, ms, L, 0, n);
    lemma_flat_idx_range(ticks, ms, L.skip(n), n);
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] crosses(ticks, ms, a[k], lim) by {}
    lemma_fillable_concat(ticks, ms, a, b, lim);
    if b.len() > 0 {
        assert(!crosses(ticks, ms, b[0], lim));
    }
}

} // verus!
