# vmatch — a formally verified matching engine

A price-time-priority limit order book whose core is written in Rust and
**proven correct with [Verus](https://github.com/verus-lang/verus)**, wrapped in
an (unverified, tested) service shell: sequencer, write-ahead journal,
snapshots, recovery and a binary TCP protocol.

```
core/      verified engine (Verus)            ~ see "Proof inventory" below
service/   journal, snapshots, sequencer, TCP server, tests, benchmarks
```

## What is proven

The proof has two layers.

**1. A reference model** (`core/src/spec.rs`): each side of the book is a
single sequence of resting orders in priority order. Matching consumes from
the front of the opposite sequence. It is small enough to read in one sitting.

Theorems about the model (`core/src/props.rs`), for every reachable state and
every command:

| Theorem | Statement |
|---|---|
| `theorem_inv` | The invariant is preserved: both sides strictly sorted by price-time priority (better price first, earlier arrival first within a price), every resting order has a valid price and quantity, ids are unique across the book, and the book is **never crossed** (best bid < best ask). |
| `theorem_new_order` | An accepted order fills **strictly in priority order** against the front of the opposite book (k-th fill is against the k-th best order, every fill but the last consumes the whole maker), **every fill is at the maker's price and within the taker's limit**, the taker's quantity is fully accounted for (filled + rested/expired), **FOK is all-or-nothing**, **post-only never takes liquidity**, and ids carry a strictly increasing sequence number. |
| `theorem_ledger` | **Quantity conservation**: resting quantity changes by exactly what the events report (+rested, −filled, −cancelled, ±reduced). |
| `theorem_reject_noop` | A rejected command changes nothing and emits only the rejection. |
| `theorem_replay_compose` / `theorem_replay_inv` | Replay is a function of the command log and is compositional: recovering from a snapshot taken after log prefix `a` and replaying `b` gives the same state and events as replaying `a ++ b`. |

**2. Refinement** (`core/src/engine.rs`): the optimised engine — a preallocated
arena of nodes threaded into intrusive doubly-linked FIFO lists per price level,
a directly indexed price ladder per side with best-level tracking, and a free
stack — is proven to compute **exactly** the model's transition:

```rust
pub fn step(&mut self, cmd: Command, out: &mut Vec<Event>)
    requires old(self).wf(),
    ensures
        self.wf(),
        self.view() == spec::step(old(self).view(), cmd).0,
        out@ == old(out)@ + spec::step(old(self).view(), cmd).1,
```

so every model theorem is a theorem about the engine. Verus additionally
proves, for all verified code: **no panics** (no out-of-bounds indexing, no
unwraps of `None`, no arithmetic overflow or underflow), and **termination of
every loop**. Snapshot `export` is proven to return exactly the abstract state;
`import` re-checks every invariant at run time and is proven to return either
`None` or a well-formed engine whose state is exactly the input.

**Determinism** follows from the refinement theorem (the engine's events and
abstract state are a function of the abstract state and the command) and is
also structural: the core is `#![no_std]`, `#![forbid(unsafe_code)]`, and uses
no clocks, randomness, hashing or threads.

## Semantics

* Prices are tick indices in `0..ticks` (the instrument's band); quantities are
  integers in `1..=2^62`.
* Order types: limit and market; time-in-force GTC, IOC, FOK, post-only.
  Market orders are matched as limit orders at the edge of the band and must
  be IOC or FOK.
* Order ids are assigned by the engine: `seq · 2^24 + slot`, where `seq` is the
  arrival sequence number (time priority) and `slot` the arena slot, giving
  O(1) cancel without a hash map. Up to 2^24 resting orders, 2^40 orders total.
* Cancel/replace: same price and quantity ≤ remaining reduces in place and
  **keeps priority**; anything else is an atomic cancel plus a new GTC (or
  post-only) order with a new id, which may match immediately.
* FOK and post-only rejections leave the book untouched and allocate no id.
* No self-trade prevention (not part of this order set).

Events: `Accepted`, `Fill{taker, maker, price, qty}`, `Rested`, `Expired`,
`Cancelled`, `Reduced`, `Rejected{reason}`.

## Trusted computing base

What you have to trust for the guarantees above to hold:

* **The model** (`spec.rs`, ~300 lines) says what you mean. Read it.
* Verus, Z3 and rustc. The proof was checked with Verus at commit `f8c9deb8`
  (Rust 1.97), Z3 4.16.0.
* `vstd`'s specifications of `Vec` (indexing, push).
* Allocation: `Vec::push` on the output event buffer may allocate; allocation
  failure aborts (outside the proof). The order arena never allocates after
  construction.

**Not verified** (tested instead): everything in `service/` — wire encoding,
the journal and its CRC framing, the snapshot file format, the sequencer's
batching and the TCP server. None of it can break the engine's invariants
(the only state transition is `Engine::step`, whose contract holds for every
input, and snapshot restore goes through the verified `import`), but bugs
there could deliver the wrong commands or lose durability.

## Running

```bash
cargo build --release
./target/release/vmatchd --listen 127.0.0.1:9100 --feed 127.0.0.1:9101 \
    --ticks 65536 --capacity 1048576 --journal /var/lib/vmatch/journal
cargo run --release -p vmatch-service --example bench     # in-process latency
cargo run --release -p vmatch-service --example loadgen -- 127.0.0.1:9100 100000
cargo test --release                                       # differential + recovery tests
```

Wire format: 24-byte command frames in, one response batch per command out
(16-byte header + 32-byte event records); see `service/src/wire.rs`.

## Re-checking the proofs

```bash
# with Verus installed (cargo-verus on PATH):
cd core && cargo verus verify
```
