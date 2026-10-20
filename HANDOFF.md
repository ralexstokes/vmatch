# Handoff: where things stand

## Status
| Area | State |
|---|---|
| `core/` (Verus spec, theorems, arena, engine, snapshot export/import) | Written, compiles as plain Rust (ghost code erased). **Proofs not yet run through Verus**: expect a round of fixes (triggers, missing asserts, small lemma gaps). |
| `service/` (wire, journal, sequencer, snapshots, TCP server) | Done; all tests pass. |
| Differential test: compiled engine vs executable transcription of the spec (`service/src/oracle.rs`) | ~1.5M random commands over 360 seeds, event-for-event identical. |
| Recovery tests | Journal replay, torn tail, mid-file corruption, snapshot + suffix: all pass. |
| Bench (noisy; ran while LLVM compiled on both cores) | ~9M cmd/s, p50 70 ns, p99 340 ns, p99.99 ~14 µs per `step()`. |

## Setting up Verus
The code targets Verus commit `f8c9deb8` (the last commit pinned to Rust 1.97.1), with vstd `=0.0.0-2026-08-30-0159` and Z3 4.16.0.

On a normal machine the release binary is the easy path. Pick the release closest to that date, or bump the `vstd` version in `core/Cargo.toml` to match the Verus you install.

```bash
cd core && cargo verus verify          # or: verus src/lib.rs --crate-type=lib
```

## Suggested order for proof fixing
1. `spec.rs`, `props.rs`: pure model plus theorems; no exec code.
2. `flat.rs`: sequence lemmas.
3. `arena.rs`: `push_back`, `unlink`, `set_qty`, `free_push`, `free_pop`, `scan`.
4. `engine.rs`: `match_exec`, `submit_exec`, `remove_exec`, `exec_*`, then the snapshot section (`export_side`, `import`, `fill_side`, `fill_free`).

Use `#[verifier::external_body]` temporarily to isolate failures. Remove every one before claiming the proof is done.

## Known follow-ups
- **Lemma placement.** `lemma_make_id` was rewritten around vstd's `lemma_fundamental_div_mod_converse`. Some lemmas call `lemma_flat_take_empty`, which is defined after its use in `engine.rs`. That is fine in Rust, but double-check visibility.
- **Tail latency.** The p99.99 tail likely comes from `scan()` when the best level empties next to a long gap (O(ticks) worst case). The planned fix is a verified 64-ary hierarchical bitmap of non-empty levels (using vstd's `u64::trailing_zeros` axioms), giving O(log64 ticks) best-level recovery.
- **Optional features.** Self-trade prevention and per-session order ownership in the gateway.
- **Re-benchmark on an idle machine** (`cargo run --release -p vmatch-service --example bench`).
