//! Verified matching-engine core.
//!
//! * `types`  — commands, events and identifiers.
//! * `spec`   — the reference model: a purely functional order book.
//! * `props`  — theorems about the reference model.
//! * `flat`   — lemmas relating per-price FIFO levels to the model's sequence.
//! * `arena`  — the allocation-free intrusive-list arena.
//! * `bitmap` — the hierarchical bitmap of non-empty levels.
//! * `engine` — the engine, proven to refine `spec::step`.
#![no_std]
#![forbid(unsafe_code)]
#![allow(
    unused_parens,
    unused_imports,
    non_snake_case,
    unused_variables,
    dead_code
)]
// Verus idioms that clippy flags: vstd's specs are stated over `Vec` (not
// slices), proof-carrying helpers take every ghost/exec component explicitly,
// loops are written in the shapes the proofs were done against, and some std
// helpers (such as `div_ceil`) have no vstd specification. Changing these for
// style would mean re-verifying, so allow them here.
#![allow(
    clippy::assign_op_pattern,
    clippy::collapsible_match,
    clippy::len_zero,
    clippy::manual_div_ceil,
    clippy::manual_range_contains,
    clippy::match_like_matches_macro,
    clippy::ptr_arg,
    clippy::too_many_arguments
)]

extern crate alloc;

pub mod arena;
pub mod bitmap;
pub mod engine;
pub mod flat;
pub mod props;
pub mod spec;
pub mod types;

pub use engine::Engine;
pub use types::*;
