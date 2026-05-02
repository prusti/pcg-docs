//! `HashSet` helpers used by generated DSL code.

use std::collections::HashSet;
use std::hash::Hash;

/// A `HashSet` containing exactly `x`.
#[must_use]
pub fn set_singleton<T: Eq + Hash + Clone>(x: &T) -> HashSet<T> {
    let mut s = HashSet::new();
    s.insert(x.clone());
    s
}
