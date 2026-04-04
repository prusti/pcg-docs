# Computing Place Capabilities

<div class="warning">

This section describes a design that is currently being implemented and is
subject to change.

</div>

In the updated design, place capabilities are _computed_ from the
[owned state](./owned-state.md) and the borrow state, rather than being
tracked and updated via explicit rules. This eliminates a class of
soundness issues (see below) and simplifies the capability accounting
logic.

## Motivation

The previous design maintained a map from places to capabilities that
was updated by three mechanisms: statement evaluation, borrow
expiry/activation, and control-flow joins. This led to three problems:

1. **Unsoundness**: the rule "when a mutable borrow expires, restore the
   place's capability to `E`" is unsound when the place has been
   conditionally moved out. After a join, the move-out information is
   lost, and the borrow expiry incorrectly restores `E` to a
   potentially uninitialised place.

2. **Insufficient annotations**: per-place capability update annotations
   (e.g. "Restore `pair.1` to `E`") do not explain the _source_ of the
   capability. Edge-oriented annotations (see
   [Edge Capabilities](./edge-capabilities.md)) address this.

3. **Complex rules**: the rules for updating capabilities were numerous
   and difficult to justify, complicating an eventual soundness proof.

## Computing Capabilities for Owned Places

The capability of an owned place $p$ is determined as follows:

1. Look up $p$ in the [initialisation state](./owned-state.md#initialisation-state).
   If $p$ is within a
   [materialised extension](./owned-state.md#materialised-extensions),
   use the initialisation capability of the ancestor leaf from which the
   extension grows.

2. Based on the initialisation capability:
   - `U` (uninitialised): the place capability is `W` (write-only).
   - `S` (shallow): the place capability is `e` (shallow exclusive).
   - Internal node: the place capability is `∅` (none), because the
     place is only partially initialised.
   - `D` (deep): proceed to check the borrow state below.

3. If the place is fully initialised (`D`), consult the borrow state:
   - If the type of $p$ contains a region $r$ but the lifetime
     projection $p \downarrow r$ does not exist in the borrow state:
     the capability is `e` (shallow exclusive).
   - If $p$ or any of its sub-places is blocked by a **mutable** borrow:
     the capability is `∅` (none).
   - If $p$ or any of its sub-places is blocked by a **shared** borrow:
     the capability is `R` (read).
   - Otherwise: the capability is `E` (exclusive).

## Computing Capabilities for Borrowed Places

For borrowed places, the capability is determined by the borrow PCG:

- If the place projects a shared borrow (e.g. `*r` where `r: &T`):
  `R` (read).
- Otherwise, if the place is a **leaf** in the borrow PCG: `E`
  (exclusive).
- Otherwise: `∅` (none).

## Example: Soundness Fix

The following example demonstrates how the computed capability approach
avoids the unsoundness of the previous design:

```rust
fn conditional_move(choice: bool) {
    let mut p = String::new();
    let mut p2 = String::new();
    let mut rp: &mut String;

    // BB0: init {p: D, p2: D, rp: U} -> cap {p: E, p2: E, rp: W}
    if true {
        consume(p);
        rp = &mut p2;
        // BB1: init {p: U, p2: D, rp: D} -> cap {p: W, p2: ∅, rp: E}
    } else {
        rp = &mut p;
        // BB2: init {p: D, p2: D, rp: D} -> cap {p: ∅, p2: E, rp: E}
    }

    // BB3: join -> init {p: U, p2: D, rp: D}
    //           -> cap  {p: ∅, p2: ∅, rp: E}

    *rp = String::from("updated");

    // After borrow expiry:
    // init {p: U, p2: D, rp: D} -> cap {p: W, p2: E, rp: e}
```

In the previous design, borrow expiry would have incorrectly restored
`p` to `E`. In the computed design, `p` remains `W` after expiry because
the initialisation state still records `p: U`.
