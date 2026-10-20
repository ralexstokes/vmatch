//! Verified matching-engine core.
//!
//! * `types`  — commands, events and identifiers.
//! * `spec`   — the reference model: a purely functional order book.
//! * `props`  — theorems about the reference model.
//! * `flat`   — lemmas relating per-price FIFO levels to the model's sequence.
//! * `arena`  — the allocation-free intrusive-list arena.
//! * `engine` — the engine, proven to refine `spec::step`.
#![no_std]
#![forbid(unsafe_code)]
#![allow(unused_parens, unused_imports, non_snake_case, unused_variables, dead_code)]

extern crate alloc;

pub mod types;
pub mod spec;
pub mod props;
pub mod flat;
pub mod arena;
pub mod engine;

pub use engine::Engine;
pub use types::*;
