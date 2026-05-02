//! Functional `HashMap` helpers.
//!
//! These mirror the Lean `Runtime/Map.lean` definitions
//! (`mapEmpty`, `mapSingleton`, `mapInsert`, …). All mutating
//! operations clone the input and return a new map so the
//! generated DSL code keeps its purely-functional flavour.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// The empty `HashMap`.
#[must_use]
pub fn map_empty<K: Eq + Hash, V>() -> HashMap<K, V> {
    HashMap::new()
}

/// A `HashMap` containing the single entry `k -> v`.
#[must_use]
pub fn map_singleton<K, V>(k: &K, v: &V) -> HashMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    let mut m = HashMap::new();
    m.insert(k.clone(), v.clone());
    m
}

/// Insert `k -> v` into a clone of `m` (overwriting any
/// existing entry) and return the result.
#[must_use]
pub fn map_insert<K, V>(m: &HashMap<K, V>, k: &K, v: &V) -> HashMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    let mut out = m.clone();
    out.insert(k.clone(), v.clone());
    out
}

/// Remove `k` from a clone of `m` and return the result. The
/// map is returned unchanged if `k` is absent.
#[must_use]
pub fn map_remove<K, V>(m: &HashMap<K, V>, k: &K) -> HashMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    let mut out = m.clone();
    out.remove(k);
    out
}

/// Look up `k` in `m`, cloning the value. The caller is
/// responsible for ensuring `k` is present (the DSL discharges
/// this via a `requires` precondition); absence panics.
#[must_use]
pub fn map_at<K, V>(m: &HashMap<K, V>, k: &K) -> V
where
    K: Eq + Hash,
    V: Clone,
{
    m[k].clone()
}

/// The values of `m`, in unspecified order.
#[must_use]
pub fn map_values<K, V>(m: &HashMap<K, V>) -> Vec<V>
where
    K: Eq + Hash,
    V: Clone,
{
    m.values().cloned().collect()
}

/// Borrowing lookup: returns `None` when `k` is absent.
#[must_use]
pub fn map_get<'a, K, V>(m: &'a HashMap<K, V>, k: &K) -> Option<&'a V>
where
    K: Eq + Hash,
{
    m.get(k)
}

/// Pointwise union of two maps from keys to sets: for keys
/// present in both maps, the values are combined with
/// `HashSet::extend`.
#[must_use]
pub fn map_union_sets<K, T>(
    m1: &HashMap<K, HashSet<T>>,
    m2: &HashMap<K, HashSet<T>>,
) -> HashMap<K, HashSet<T>>
where
    K: Eq + Hash + Clone,
    T: Eq + Hash + Clone,
{
    let mut out: HashMap<K, HashSet<T>> = m1.clone();
    for (k, v) in m2 {
        out.entry(k.clone())
            .and_modify(|e| e.extend(v.iter().cloned()))
            .or_insert_with(|| v.clone());
    }
    out
}
