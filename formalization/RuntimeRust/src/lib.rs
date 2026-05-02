//! Source-of-truth runtime helpers for the generated PCG Rust
//! crates. Mirrors the role of `Runtime/{Map,Set}.lean` on the
//! Lean side: a single hand-written copy of the helpers that the
//! DSL emits calls to, copied verbatim into the generated
//! workspace at export time.

#![deny(clippy::all)]
#![deny(clippy::pedantic)]
// Generated DSL code only ever produces `HashMap` / `HashSet`
// with the default hasher; generalizing over `BuildHasher`
// would be dead generality.
#![allow(clippy::implicit_hasher)]

pub mod list;
pub mod map;
pub mod set;
