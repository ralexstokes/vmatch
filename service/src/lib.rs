//! Unverified shell around the verified `vmatch-core` engine: wire protocol,
//! write-ahead journal, sequencer with replay recovery, and a TCP server.
//!
//! Nothing in this crate can violate the engine's proven properties: the only
//! way to change engine state is `Engine::step`, whose contract holds for any
//! input. What this crate is responsible for (and is tested, not proven) is
//! delivering the right commands in the right order and durably recording them.

pub mod journal;
#[doc(hidden)]
pub mod oracle;
pub mod sequencer;
pub mod server;
pub mod snapshot;
pub mod wire;
