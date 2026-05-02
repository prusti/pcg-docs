//! Functional list helpers operating on `&[T]` and returning
//! freshly-allocated `Vec<T>`s, matching the purely-functional
//! flavour of the DSL.

/// The last element of `xs`, cloned, or `None` if empty.
#[must_use]
pub fn last<T: Clone>(xs: &[T]) -> Option<T> {
    xs.last().cloned()
}

/// A vector of length `n` whose entries are all clones of `x`.
#[must_use]
pub fn replicate<T: Clone>(n: &usize, x: &T) -> Vec<T> {
    vec![x.clone(); *n]
}

/// `xs` with the entry at index `i` overwritten by a clone of
/// `x`. Returns a clone of `xs` unchanged when `i` is out of
/// range.
#[must_use]
pub fn list_set<T: Clone>(xs: &[T], i: &usize, x: &T) -> Vec<T> {
    let mut v: Vec<T> = xs.to_vec();
    if *i < v.len() {
        v[*i] = x.clone();
    }
    v
}

/// The first `n` elements of `xs`, cloned. If `n` exceeds the
/// length of `xs`, the entire slice is returned.
#[must_use]
pub fn list_take<T: Clone>(n: &usize, xs: &[T]) -> Vec<T> {
    xs.iter().take(*n).cloned().collect()
}

/// `xs` with its first `n` elements removed, cloned. Returns
/// an empty vector when `n` exceeds the length of `xs`.
#[must_use]
pub fn list_drop<T: Clone>(n: &usize, xs: &[T]) -> Vec<T> {
    xs.iter().skip(*n).cloned().collect()
}
