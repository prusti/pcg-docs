# Edge Capabilities

<div class="warning">

This section describes a design that is currently being implemented and is
subject to change.

</div>

In the updated design, edges in the Owned PCG (specifically, unpack
hyperedges) carry an _edge capability_ that describes whether the
expansion is mutable or immutable. This is used to generate
upgrade/downgrade annotations when the mutability of an edge changes
between PCG states.

## Edge Capability Values

An edge capability is one of:

- **Immutable (`I`)**: the expansion is under a shared borrow. The
  parent place has capability `R`, and the children inherit `R`.
- **Mutable (`M`)**: the expansion is not constrained by a shared
  borrow. Children may have capabilities `E`, `W`, or `e` depending
  on their initialisation state.

## Computing Edge Capabilities

Edge capabilities are _computed_, not tracked explicitly. An edge's
capability is determined by the borrow state: if any place in the
subtree rooted at the parent of the edge is blocked by a shared
(immutable) borrow, the edge is `I`; otherwise it is `M`.

## Annotations from Edge Capability Changes

When the edge capability of an unpack hyperedge changes between two
consecutive PCG states (e.g. from `I` to `M` because a shared borrow
expired), an _upgrade_ annotation is emitted. Conversely, when an edge
transitions from `M` to `I` (e.g. because a shared borrow is created),
a _downgrade_ annotation is emitted.

These edge-oriented annotations replace the previous per-place capability
update annotations (such as "Restore `pair.1` to `E`"). The advantage is
that edge annotations make explicit _where_ a capability change
originates, rather than describing isolated per-place updates whose
source is implicit.

### Example

Consider the following program:

```rust
fn shared_borrow() {
    let mut pair = (String::new(), String::new());
    // {pair: D} -> {pair: E}

    let r0 = &pair.0;
    // edge {pair} -> {.0, .1}: I
    // {r0: E, pair: R, pair.0: R, pair.1: R}

    let p1 = pair.1;
    // edge {pair} -> {.0, .1}: M   (upgrade emitted)
    // {r0: E, pair: ∅, pair.0: R, pair.1: W}
}
```

When `pair.1` is moved, the shared borrow on `pair.0` no longer covers
`pair` as a whole, so the edge `{pair} -> {.0, .1}` is upgraded from `I`
to `M`, and an `upgrade {pair} -> {.0, .1}` annotation is emitted.
