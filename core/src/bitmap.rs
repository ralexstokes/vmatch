//! A 64-ary hierarchical bitmap over the levels of one ladder side: layer 0
//! has a bit per level (set iff the level is non-empty), and each higher layer
//! has a bit per word of the layer below (set iff that word is non-zero). Four
//! layers cover `64^4 = MAX_TICKS` levels, so finding the first non-empty level
//! at or after any index takes a constant number of word operations, however
//! far away it is.

use crate::types::*;
use alloc::vec::Vec;
use vstd::prelude::*;
// Only proofs refer to these, and they exist only when building under Verus.
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::{axiom_u64_trailing_zeros, u64_trailing_zeros};

verus! {

pub struct Bitmap {
    pub l0: Vec<u64>,
    pub l1: Vec<u64>,
    pub l2: Vec<u64>,
    pub l3: Vec<u64>,
}

// ---------------------------------------------------------------------------
// Specification.

pub open spec fn bit(w: u64, b: int) -> bool {
    (w >> (b as u64)) & 1u64 == 1u64
}

/// Number of words needed for `n` bits.
pub open spec fn nwords(n: int) -> int {
    (n + 63) / 64
}

/// `words` holds exactly the set `ne`, one bit per element, padding clear.
pub open spec fn layer_ok(words: Seq<u64>, ne: Seq<bool>) -> bool {
    &&& words.len() == nwords(ne.len() as int)
    &&& forall|w: int, b: int| 0 <= w < words.len() && 0 <= b < 64 ==>
        #[trigger] bit(words[w], b) == (64 * w + b < ne.len() && ne[64 * w + b])
}

/// Which words of a layer are non-zero: the set the layer above holds.
pub open spec fn summary(words: Seq<u64>) -> Seq<bool> {
    Seq::new(words.len(), |w: int| words[w] != 0)
}

pub open spec fn bitmap_wf(bm: Bitmap, ne: Seq<bool>) -> bool {
    &&& 1 <= ne.len() <= MAX_TICKS
    &&& layer_ok(bm.l0@, ne)
    &&& layer_ok(bm.l1@, summary(bm.l0@))
    &&& layer_ok(bm.l2@, summary(bm.l1@))
    &&& layer_ok(bm.l3@, summary(bm.l2@))
}

/// `r` is the first element of `ne` at or after `from` that is set, or
/// `ne.len()` if there is none.
pub open spec fn first_from(ne: Seq<bool>, from: int, r: int) -> bool {
    &&& 0 <= from <= r <= ne.len()
    &&& forall|i: int| from <= i < r ==> !(#[trigger] ne[i])
    &&& r < ne.len() ==> ne[r]
}

// ---------------------------------------------------------------------------
// Single-word facts.

proof fn lemma_bit_set(x: u64, b: u64, c: u64)
    requires b < 64, c < 64,
    ensures bit(x | (1u64 << b), c as int) == (bit(x, c as int) || c == b),
{
    assert(((x | (1u64 << b)) >> c) & 1u64 == 1u64 <==> (((x >> c) & 1u64 == 1u64) || c == b)) by (bit_vector)
        requires b < 64, c < 64;
}

proof fn lemma_bit_clear(x: u64, b: u64, c: u64)
    requires b < 64, c < 64,
    ensures bit(x & !(1u64 << b), c as int) == (bit(x, c as int) && c != b),
{
    assert(((x & !(1u64 << b)) >> c) & 1u64 == 1u64 <==> (((x >> c) & 1u64 == 1u64) && c != b)) by (bit_vector)
        requires b < 64, c < 64;
}

proof fn lemma_bit_mask(x: u64, s: u64, c: u64)
    requires s < 64, c < 64,
    ensures bit(x & (0xffff_ffff_ffff_ffffu64 << s), c as int) == (bit(x, c as int) && c >= s),
{
    assert(((x & (0xffff_ffff_ffff_ffffu64 << s)) >> c) & 1u64 == 1u64 <==> (((x >> c) & 1u64 == 1u64) && c >= s)) by (bit_vector)
        requires s < 64, c < 64;
}

proof fn lemma_bit_nonzero(x: u64, c: u64)
    requires c < 64, bit(x, c as int),
    ensures x != 0,
{
    assert((x >> c) & 1u64 == 1u64 ==> x != 0) by (bit_vector);
}

proof fn lemma_bit_zero(c: u64)
    requires c < 64,
    ensures !bit(0, c as int),
{
    assert((0u64 >> c) & 1u64 != 1u64) by (bit_vector);
}

/// The lowest set bit of a non-zero word.
proof fn lemma_tz(x: u64)
    requires x != 0,
    ensures
        u64_trailing_zeros(x) < 64,
        bit(x, u64_trailing_zeros(x) as int),
        forall|c: int| 0 <= c < u64_trailing_zeros(x) ==> !#[trigger] bit(x, c),
{
    axiom_u64_trailing_zeros(x);
    assert forall|c: int| 0 <= c < u64_trailing_zeros(x) implies !#[trigger] bit(x, c) by {
        assert((x >> (c as u64)) & 1u64 == 0u64);
    }
}

// ---------------------------------------------------------------------------
// Layer lemmas.

/// The words of a layer are non-zero exactly where the set has an element.
proof fn lemma_word_zero(words: Seq<u64>, ne: Seq<bool>, w: int)
    requires layer_ok(words, ne), 0 <= w < words.len(), words[w] == 0,
    ensures forall|i: int| 64 * w <= i < 64 * w + 64 && i < ne.len() ==> !#[trigger] ne[i],
{
    assert forall|i: int| 64 * w <= i < 64 * w + 64 && i < ne.len() implies !#[trigger] ne[i] by {
        let b = i - 64 * w;
        lemma_bit_zero(b as u64);
        assert(bit(words[w], b) == (64 * w + b < ne.len() && ne[64 * w + b]));
    }
}

/// From the first set word at or after `s` in the layer above, to the first
/// set element at or after `64 * s` in this layer.
proof fn lemma_descend(words: Seq<u64>, ne: Seq<bool>, s: int, j: int)
    requires
        layer_ok(words, ne),
        0 <= s < words.len(),
        first_from(summary(words), s, j),
    ensures
        64 * s < ne.len(),
        j < words.len() ==> {
            let r = 64 * j + u64_trailing_zeros(words[j]);
            &&& r < ne.len()
            &&& first_from(ne, 64 * s, r)
        },
        j == words.len() ==> first_from(ne, 64 * s, ne.len() as int),
{
    let sm = summary(words);
    assert forall|i: int| 64 * s <= i < 64 * j && i < ne.len() implies !#[trigger] ne[i] by {
        let w = i / 64;
        assert(!sm[w]);
        lemma_word_zero(words, ne, w);
    }
    if j < words.len() {
        let x = words[j];
        assert(sm[j]);
        lemma_tz(x);
        let tz = u64_trailing_zeros(x) as int;
        let r = 64 * j + tz;
        assert(bit(x, tz));
        assert forall|i: int| 64 * s <= i < r implies !#[trigger] ne[i] by {
            if i >= 64 * j {
                assert(!bit(x, i - 64 * j));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Layer operations.

/// Add element `i` to the set a layer holds.
fn layer_set(words: &mut Vec<u64>, Ghost(ne): Ghost<Seq<bool>>, i: u32) -> (was_zero: bool)
    requires
        layer_ok(old(words)@, ne),
        i < ne.len(),
    ensures
        layer_ok(final(words)@, ne.update(i as int, true)),
        summary(final(words)@) == summary(old(words)@).update(i as int / 64, true),
        was_zero == !summary(old(words)@)[i as int / 64],
{
    let ghost w0 = words@;
    let w = (i / 64) as usize;
    let b = i % 64;
    let x = words[w];
    let y = x | (1u64 << (b as u64));
    words.set(w, y);
    proof {
        let ne2 = ne.update(i as int, true);
        assert forall|ww: int, c: int| 0 <= ww < words@.len() && 0 <= c < 64 implies
            #[trigger] bit(words@[ww], c) == (64 * ww + c < ne2.len() && ne2[64 * ww + c]) by {
            if ww == w as int {
                lemma_bit_set(x, b as u64, c as u64);
                assert(bit(w0[ww], c) == (64 * ww + c < ne.len() && ne[64 * ww + c]));
            } else {
                assert(bit(w0[ww], c) == (64 * ww + c < ne.len() && ne[64 * ww + c]));
            }
        }
        lemma_bit_set(x, b as u64, b as u64);
        lemma_bit_nonzero(y, b as u64);
        assert(summary(words@) =~= summary(w0).update(i as int / 64, true));
    }
    x == 0
}

/// Remove element `i` from the set a layer holds.
fn layer_clear(words: &mut Vec<u64>, Ghost(ne): Ghost<Seq<bool>>, i: u32) -> (now_zero: bool)
    requires
        layer_ok(old(words)@, ne),
        i < ne.len(),
    ensures
        layer_ok(final(words)@, ne.update(i as int, false)),
        summary(final(words)@) == summary(old(words)@).update(i as int / 64, !now_zero),
        !now_zero ==> summary(old(words)@)[i as int / 64],
{
    let ghost w0 = words@;
    let w = (i / 64) as usize;
    let b = i % 64;
    let x = words[w];
    let y = x & !(1u64 << (b as u64));
    words.set(w, y);
    proof {
        let ne2 = ne.update(i as int, false);
        assert forall|ww: int, c: int| 0 <= ww < words@.len() && 0 <= c < 64 implies
            #[trigger] bit(words@[ww], c) == (64 * ww + c < ne2.len() && ne2[64 * ww + c]) by {
            if ww == w as int {
                lemma_bit_clear(x, b as u64, c as u64);
                assert(bit(w0[ww], c) == (64 * ww + c < ne.len() && ne[64 * ww + c]));
            } else {
                assert(bit(w0[ww], c) == (64 * ww + c < ne.len() && ne[64 * ww + c]));
            }
        }
        assert(summary(words@) =~= summary(w0).update(i as int / 64, y != 0));
        let bb = b as u64;
        assert(x & !(1u64 << bb) != 0 ==> x != 0) by (bit_vector);
    }
    y == 0
}

/// The first element at or after `from` within `from`'s word, if any.
fn scan_word(words: &Vec<u64>, Ghost(ne): Ghost<Seq<bool>>, from: u32) -> (r: (bool, u32))
    requires
        layer_ok(words@, ne),
        from < ne.len(),
        ne.len() <= MAX_TICKS,
    ensures
        r.0 ==> r.1 < ne.len() && first_from(ne, from as int, r.1 as int),
        !r.0 ==> forall|i: int| from <= i < 64 * (from / 64 + 1) && i < ne.len() ==> !#[trigger] ne[i],
{
    let w = (from / 64) as usize;
    let s = from % 64;
    let m = words[w] & (0xffff_ffff_ffff_ffffu64 << (s as u64));
    proof {
        assert forall|c: int| 0 <= c < 64 implies #[trigger] bit(m, c) == (bit(words@[w as int], c) && c >= s) by {
            lemma_bit_mask(words@[w as int], s as u64, c as u64);
        }
    }
    if m == 0 {
        proof {
            assert forall|i: int| from <= i < 64 * (from / 64 + 1) && i < ne.len() implies !#[trigger] ne[i] by {
                let c = i - 64 * w;
                lemma_bit_zero(c as u64);
                assert(bit(words@[w as int], c) == (64 * w + c < ne.len() && ne[64 * w + c]));
            }
        }
        (false, 0)
    } else {
        let tz = m.trailing_zeros();
        proof {
            lemma_tz(m);
            assert(bit(words@[w as int], tz as int));
            assert forall|i: int| from <= i < 64 * w + tz implies !#[trigger] ne[i] by {
                let c = i - 64 * w;
                assert(!bit(m, c));
                assert(bit(words@[w as int], c) == (64 * w + c < ne.len() && ne[64 * w + c]));
            }
        }
        (true, (w as u32) * 64 + tz)
    }
}

/// From the first set word `j` at or after `s` in the layer above (or the
/// layer's length if none), to the first element at or after `64 * s` here.
fn descend(words: &Vec<u64>, Ghost(ne): Ghost<Seq<bool>>, n: u32, s: u32, j: u32) -> (r: u32)
    requires
        layer_ok(words@, ne),
        n == ne.len(),
        ne.len() <= MAX_TICKS,
        s < words@.len(),
        first_from(summary(words@), s as int, j as int),
    ensures
        first_from(ne, 64 * s, r as int),
{
    proof { lemma_descend(words@, ne, s as int, j as int); }
    if j as usize == words.len() {
        n
    } else {
        proof { lemma_tz(words@[j as int]); }
        j * 64 + words[j as usize].trailing_zeros()
    }
}

proof fn lemma_first_extend(ne: Seq<bool>, from: int, mid: int, r: int)
    requires
        0 <= from <= mid,
        forall|i: int| from <= i < mid && i < ne.len() ==> !#[trigger] ne[i],
        first_from(ne, mid, r),
    ensures
        first_from(ne, from, r),
{
}

/// Layer sizes: each layer has `nwords` of the one below, and the top fits in
/// one word because `ne.len() <= 64^4`.
proof fn lemma_sizes(n: int)
    requires 1 <= n <= MAX_TICKS,
    ensures
        1 <= nwords(n) <= 262144,
        1 <= nwords(nwords(n)) <= 4096,
        1 <= nwords(nwords(nwords(n))) <= 64,
        nwords(nwords(nwords(nwords(n)))) == 1,
{
}

impl Bitmap {
    /// An empty bitmap for `n` levels.
    pub fn new(n: u32) -> (bm: Bitmap)
        requires 1 <= n <= MAX_TICKS,
        ensures bitmap_wf(bm, Seq::new(n as nat, |t: int| false)),
    {
        proof { lemma_sizes(n as int); }
        let n0 = (n + 63) / 64;
        let n1 = (n0 + 63) / 64;
        let n2 = (n1 + 63) / 64;
        let l0 = zeros(n0);
        let l1 = zeros(n1);
        let l2 = zeros(n2);
        let l3 = zeros(1);
        let bm = Bitmap { l0, l1, l2, l3 };
        proof {
            let ne = Seq::new(n as nat, |t: int| false);
            lemma_zeros_ok(bm.l0@, ne);
            assert(summary(bm.l0@) =~= Seq::new(n0 as nat, |t: int| false));
            lemma_zeros_ok(bm.l1@, summary(bm.l0@));
            assert(summary(bm.l1@) =~= Seq::new(n1 as nat, |t: int| false));
            lemma_zeros_ok(bm.l2@, summary(bm.l1@));
            assert(summary(bm.l2@) =~= Seq::new(n2 as nat, |t: int| false));
            lemma_zeros_ok(bm.l3@, summary(bm.l2@));
        }
        bm
    }

    /// Mark level `t` non-empty.
    pub fn set(&mut self, Ghost(ne): Ghost<Seq<bool>>, t: u32)
        requires bitmap_wf(*old(self), ne), t < ne.len(),
        ensures bitmap_wf(*final(self), ne.update(t as int, true)),
    {
        let ghost s0 = summary(self.l0@);
        let ghost s1 = summary(self.l1@);
        let ghost s2 = summary(self.l2@);
        proof { lemma_sizes(ne.len() as int); }
        let i1 = t / 64;
        let i2 = i1 / 64;
        let i3 = i2 / 64;
        let z0 = layer_set(&mut self.l0, Ghost(ne), t);
        if z0 {
            let z1 = layer_set(&mut self.l1, Ghost(s0), i1);
            if z1 {
                let z2 = layer_set(&mut self.l2, Ghost(s1), i2);
                if z2 {
                    layer_set(&mut self.l3, Ghost(s2), i3);
                } else {
                    proof { assert(summary(self.l2@) =~= s2); }
                }
            } else {
                proof { assert(summary(self.l1@) =~= s1); }
            }
        } else {
            proof { assert(summary(self.l0@) =~= s0); }
        }
    }

    /// Mark level `t` empty.
    pub fn clear(&mut self, Ghost(ne): Ghost<Seq<bool>>, t: u32)
        requires bitmap_wf(*old(self), ne), t < ne.len(),
        ensures bitmap_wf(*final(self), ne.update(t as int, false)),
    {
        let ghost s0 = summary(self.l0@);
        let ghost s1 = summary(self.l1@);
        let ghost s2 = summary(self.l2@);
        proof { lemma_sizes(ne.len() as int); }
        let i1 = t / 64;
        let i2 = i1 / 64;
        let i3 = i2 / 64;
        let z0 = layer_clear(&mut self.l0, Ghost(ne), t);
        if z0 {
            let z1 = layer_clear(&mut self.l1, Ghost(s0), i1);
            if z1 {
                let z2 = layer_clear(&mut self.l2, Ghost(s1), i2);
                if z2 {
                    layer_clear(&mut self.l3, Ghost(s2), i3);
                } else {
                    proof { lemma_set_present(self.l3@, s2, i3 as int); }
                }
            } else {
                proof { lemma_set_present(self.l2@, s1, i2 as int); }
            }
        } else {
            proof { lemma_set_present(self.l1@, s0, i1 as int); }
        }
    }

    /// The first non-empty level at or after `from`, or `n` (the number of
    /// levels) if there is none.
    pub fn next(&self, Ghost(ne): Ghost<Seq<bool>>, n: u32, from: u32) -> (r: u32)
        requires bitmap_wf(*self, ne), n == ne.len(), from <= n,
        ensures first_from(ne, from as int, r as int),
    {
        proof { lemma_sizes(n as int); }
        let ghost s0 = summary(self.l0@);
        let ghost s1 = summary(self.l1@);
        let ghost s2 = summary(self.l2@);
        if from >= n {
            return n;
        }
        let (f, r) = scan_word(&self.l0, Ghost(ne), from);
        if f {
            return r;
        }
        // Nothing more in `from`'s word: continue from the next word.
        let n0 = self.l0.len() as u32;
        let a1 = from / 64 + 1;
        if a1 >= n0 {
            return n;
        }
        let (f, r) = scan_word(&self.l1, Ghost(s0), a1);
        if f {
            let r0 = descend(&self.l0, Ghost(ne), n, a1, r);
            proof { lemma_first_extend(ne, from as int, 64 * a1, r0 as int); }
            return r0;
        }
        let n1 = self.l1.len() as u32;
        let a2 = a1 / 64 + 1;
        if a2 >= n1 {
            proof { lemma_first_extend(s0, a1 as int, n0 as int, n0 as int); }
            let r0 = descend(&self.l0, Ghost(ne), n, a1, n0);
            proof { lemma_first_extend(ne, from as int, 64 * a1, r0 as int); }
            return r0;
        }
        let (f, r) = scan_word(&self.l2, Ghost(s1), a2);
        let n2 = self.l2.len() as u32;
        let a3 = a2 / 64 + 1;
        let j2 = if f {
            r
        } else if a3 >= n2 {
            n1
        } else {
            let (f3, r3) = scan_word(&self.l3, Ghost(s2), a3);
            let j3 = if f3 { r3 } else { n2 };
            proof {
                if !f3 { lemma_first_extend(s2, a3 as int, n2 as int, n2 as int); }
            }
            let j2 = descend(&self.l2, Ghost(s1), n1, a3, j3);
            proof { lemma_first_extend(s1, a2 as int, 64 * a3, j2 as int); }
            j2
        };
        proof {
            if !f && a3 >= n2 { lemma_first_extend(s1, a2 as int, n1 as int, n1 as int); }
        }
        let j1 = descend(&self.l1, Ghost(s0), n0, a2, j2);
        proof { lemma_first_extend(s0, a1 as int, 64 * a2, j1 as int); }
        let r0 = descend(&self.l0, Ghost(ne), n, a1, j1);
        proof { lemma_first_extend(ne, from as int, 64 * a1, r0 as int); }
        r0
    }
}

/// Clearing a bit whose word stays non-zero leaves the summary unchanged.
proof fn lemma_set_present(upper: Seq<u64>, sm: Seq<bool>, j: int)
    requires layer_ok(upper, sm), 0 <= j < sm.len(), sm[j],
    ensures layer_ok(upper, sm.update(j, true)),
{
    assert(sm.update(j, true) =~= sm);
}

fn zeros(n: u32) -> (v: Vec<u64>)
    ensures v@.len() == n, forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0,
{
    let mut v: Vec<u64> = Vec::with_capacity(n as usize);
    let mut i: u32 = 0;
    while i < n
        invariant i <= n, v@.len() == i, forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == 0,
        decreases n - i,
    {
        v.push(0);
        i = i + 1;
    }
    v
}

proof fn lemma_zeros_ok(words: Seq<u64>, ne: Seq<bool>)
    requires
        words.len() == nwords(ne.len() as int),
        forall|i: int| 0 <= i < words.len() ==> #[trigger] words[i] == 0,
        forall|i: int| 0 <= i < ne.len() ==> !#[trigger] ne[i],
    ensures layer_ok(words, ne),
{
    assert forall|w: int, b: int| 0 <= w < words.len() && 0 <= b < 64 implies
        #[trigger] bit(words[w], b) == (64 * w + b < ne.len() && ne[64 * w + b]) by {
        lemma_bit_zero(b as u64);
    }
}

} // verus!
