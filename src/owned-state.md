# Owned State

<div class="warning">

This section describes a design that is currently being implemented and is
subject to change.

</div>

The _Owned State_ describes the state of owned places at a program point.
It consists of two layers:

1. The **Initialisation State**, which tracks which owned places are
   initialised, uninitialised, or shallowly initialised.
2. **Materialised extensions**, which extend the leaves of the
   initialisation state to reach the roots of borrows in the borrow PCG.

Place capabilities are _computed_ from the owned state and the borrow
state (see [Computing Place Capabilities](./computing-place-capabilities.md)),
rather than being stored and updated directly.

The key motivation for this design is that the initialisation state does
not depend on what places are borrowed. This independence simplifies the
join algorithm significantly, because borrows no longer force the owned
state to be unpacked in borrow-dependent ways.

## Initialisation State

### Initialisation Capabilities

Each leaf node in the initialisation state carries one of three
_initialisation capabilities_, ordered as $D > S > U$:

#### Deep (`D`)

The place is fully initialised. All memory reachable from this place
(including through dereferences) is valid and accessible. This is the
state of a place after it has been assigned a value.

#### Shallow (`S`)

The place is shallowly initialised: the place itself holds a valid
value, but memory behind a dereference may not be initialised. This
state arises only for `Box`-typed places, where the heap allocation
exists but no value has been written through the pointer yet.

#### Uninit (`U`)

The place is uninitialised or has been moved out of. No reads are
permitted; only writes (to re-initialise the place) are allowed.

### Tree Structure

The initialisation state is a forest of trees, one per allocated MIR
local. The root of each tree is a local variable, and internal nodes
correspond to place expansions (unpacking a struct or tuple into its
fields).

The key structural properties are:

- **Leaf nodes** carry an initialisation capability (`D`, `S`, or `U`).
- **Internal nodes** have no explicit capability; their capability is
  derived from their children. An internal node exists only because one
  or more of its descendants has a different initialisation status than
  its siblings.
- **Invariant**: if a tree is expanded (i.e. is not a single leaf node),
  then at least one of its leaves must be `U` or `S`. Otherwise, the
  tree would be collapsed to a single `D` leaf.

For example, after executing `consume(pair.0)` on a `pair: (String, String)`:

```text
pair
├── .0: U
└── .1: D
```

The tree is expanded because `pair.0` has been moved out while `pair.1`
remains initialised.

In contrast, a fully initialised pair is represented as a single leaf:

```text
pair: D
```

### Join Algorithm

The join algorithm on the initialisation state operates pointwise on the
tree structure. Because the initialisation state is independent of
borrows, the join does not need to consult the borrow state.

The algorithm is defined recursively:

$$\text{join}(\text{leaf}(s_1), \text{leaf}(s_2)) = \text{leaf}(\min(s_1, s_2))$$

$$\text{join}(\text{leaf}(S), \text{internal}(n)) = \text{leaf}(S)$$

$$\text{join}(\text{leaf}(U), \text{internal}(n)) = \text{leaf}(U)$$

$$\text{join}(\text{leaf}(D), \text{internal}(n)) = \text{internal}(n)$$

$$\text{join}(\text{internal}(m), \text{internal}(n)) = \text{internal}(\text{join}(m_0, n_0), \text{join}(m_1, n_1), \ldots)$$

The intuition behind these cases:

- **Two leaves**: take the minimum capability. If either side is
  uninitialised, the join must conservatively assume the place may be
  uninitialised.
- **Leaf `U` or `S` vs internal**: the leaf dominates because if the
  place is (at best) uninitialised or shallowly initialised, the
  detailed expansion on the other side is irrelevant.
- **Leaf `D` vs internal**: the internal node's structure is preserved,
  because a deeply initialised place is compatible with any expansion
  of that place.
- **Two internals**: join children pointwise.

#### Example

Consider the following program:

```rust
type Pair = (String, String);

fn f(choice: bool) {
    let mut pair0 = (String::new(), String::new());
    let mut pair1 = (String::new(), String::new());
    let mut pair2: Pair;
    let mut rx: String;
    if choice {
        rx = pair0.0;
        pair2 = pair1; // {pair0: {.0: U, .1: D}, pair1: U}
    } else {
        rx = pair1.0;
        pair2 = pair0; // {pair0: U, pair1: {.0: U, .1: D}}
    }
    // join: {pair0: U, pair1: U}
}
```

At the join point, `pair0` has state `{.0: U, .1: D}` on one branch and
`U` on the other. Applying the rule
$\text{join}(\text{leaf}(U), \text{internal}(n)) = \text{leaf}(U)$,
the result is `pair0: U`. Symmetrically, `pair1: U`.

## Materialised Extensions

The leaves of the initialisation state serve as the roots of
_materialised extensions_. A materialised extension is an additional
subtree that grows off a leaf of the initialisation state to reach
places that are targets of borrows in the borrow PCG.

Materialised extensions exist because borrowing a sub-place does not
change the initialisation state (e.g. `&mut x.f` does not expand `x` in
the init state), but the owned state still needs to represent the
expanded structure so that the borrow target is a node in the graph.

### Construction

For each leaf $l$ of the initialisation state with place $p$, if there
exist places $q_1, \ldots, q_n$ in the borrow PCG that are strict
descendants of $p$ (i.e. $p$ is a strict prefix of each $q_i$), then a
materialised extension tree is constructed by expanding $p$ toward each
$q_i$. The materialised extension tree uses the same expansion structure
as owned place expansions. Leaves of the materialised extension carry
no additional data.

### Example

Suppose `x.0` is moved out and `x.1` is `D`, and there is a borrow
targeting `x.1.h`:

```text
Initialisation state:
  x
  ├── .0: U
  └── .1: D

Materialised extension off x.1:
  x.1
  └── .h  (materialised)
```

The full owned state combines both: the init state provides the tree
`x -> {x.0, x.1}`, and the materialised extension provides the edge
`x.1 -> {x.1.h}`.

A simpler example where the init state is not expanded:

```rust
let mut pair = (String::new(), String::new());
let rx = &mut pair.0;
// init state: {pair: D}
// materialised: pair -> {pair.0, pair.1}
```

Here the initialisation state is a single leaf `{pair: D}` (borrowing
does not change initialisation), but the materialised extension expands
`pair` so that `pair.0` (the borrow target) is a node in the owned
state.
