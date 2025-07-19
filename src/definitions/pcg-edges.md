# PCG Hyperedges

A PCG Hyperedge is a directed edge of the form $\overline{n_s} \rightarrow
\overline{n_t}$, where elements of $\overline{n_s}$ and $\overline{n_t}$ are PCG
nodes. The set $\overline{n_s}$ are referred to as the _source nodes_ of the
edge, and $\overline{n_t}$ are the _target nodes. Hyperedges in the PCG are
labelled with [validity conditions](./validity-conditions.md)[^owned].

[^owned]: Currently not in the owned portion of the PCG, but this should happen eventually.

We currently define the following edge types:

## Unpack Edges

Unpack edges are used to represent the unpack of an _owned_ place in order to
access one of its fields. For example, writing to a field `x.f` requires
expanding `x`.

An unpack edge connects an _owned_ place $p$ to one of it's
[expansions](./places.html#place-expansion) $\overline{p}$.
Each place in $\overline{p}$ is guaranteed to be owned.

For example, if `x` is an owned place with fields `x.f` and `x.g`, the edge
`{x} -> {x.f, x.g}` is a valid unpack edge.

Unpack edges are _not_ generated for dereferences of reference-typed places.
[Borrow PCG Expansion Edges](#borrow-pcg-expansion-edge) are used in such cases.
Unpack edges are used in derefences of `Box`-typed places.

<div class="warning">

In the implementation, we don't have an explicit data type representing unpack
edges. Rather, the unpack edges are conceptually represented as the interior
edges in the Owned PCG.

Validity conditions are not currently associated with unpack edges in the
implementation.

</div>

## Borrow PCG Expansion Edge

Borrow PCG Expansion Edges conceptually take one of three forms:

- _Dereference Expansion_: The dereference of a reference-typed place
- _Place Expansion_: The expansion of a borrowed place to access one of its fields
- _Lifetime Projection Expansion_: The expansion of the lifetime projections of an owned or borrowed place

### Dereference Expansion

The _source nodes_ of a dereference expansion consist of:

- A _maybe-labelled_ place $\maybelabelled_s$, and:
- A lifetime projection $\lifetimeproj_s$

Where $\maybelabelled_s$ and $\lifetimeproj_s$ have the same associated place $p_s$.

The _target node_ $\maybelabelled_t$ of a dereference expansion is a
maybe-labelled place with associated place $*p_s$.

### Place Expansion

The _source node_ of a place expansion is a maybe-labelled place
$\maybelabelled_s$ with associated place $p_s$, where $p_s$ is a borrowed place
and $p_s$ is not a reference.

The _target nodes_ of a place expansion is a set of maybe-labelled places
$\overline{\maybelabelled_t}$ where the associated places of
$\overline{\maybelabelled_t}$ are an expansion of $p_s$.

### Lifetime Projection Expansion

The _source node_ of a lifetime projection expansion is a lifetime projection
$\lifetimeproj_s$ where $\base(\lifetimeproj_s)$ is a maybe-labelled place $\maybelabelled_s$ with associated place of $p_s$.

The _target nodes_ of a lifetime projection expansion is a set of lifetime
projections $\overline{\lifetimeproj_t}$ where the base of each place is a
maybe-labelled place. The associated places of the bases of
$\overline{\lifetimeproj_t}$ are an expansion of $p_s$.

<div class="warning">

It might make sense to differentiate lifetime projection expansions of owned and
borrowed places, since they differ in terms of how placeholder labels should be
included. Namely, for owned places there is no need to connect the expansion
nodes to the placeholder of the base node (the owned place may never be
repacked, or could be repacked with entirely unrelated lifetime projections)

</div>

## Borrow Edges

Borrow edges are used to represent direct borrows in the program. We define two types:

- _Local Borrow Edges_: A borrow created in the MIR Body,
  e.g. from a statement `let y = &mut x;`
- _Remote Borrow Edges_: A borrow created by the _caller_ of this function where the assigned place of the borrow is an input to this function.

Remote Borrows are named as such because (unlike local borrows), the borrowed
place does not have a name in the MIR body (since it was created by the caller).

### Local Borrows

The _source node_ of a local borrow is a maybe-labelled place $\maybelabelled$.
The _target node_ of a local borrow is a lifetime projection $\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

### Remote Borrows

The _source node_ of a remote borrow is a remote place $\remote{\local}$.
The _target node_ of a remote borrow is a lifetime projection $\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

## Abstraction Edge

An abstraction edge represents the flow of borrows introduced due to a function
call or loop.

### Function Call Abstraction Edge

The _source node_ of a function call abstraction edge is a lifetime projection
$\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

The _target node_ of a function call abstraction edge is a lifetime projection
$\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

### Loop Abstraction Edge

The _source node_ of a loop abstraction edge is a PCG node.

The _target node_ of a loop abstraction edge is a [local PCG
node](pcg-nodes.html#local-pcg-nodes).

## Borrow-Flow Edge

A borrow-flow edge represents the flow of borrows between a lifetime projection
$\lifetimeproj_s$ and a [local](pcg-nodes.html#local-pcg-nodes) lifetime
projection $\lifetimeproj_t$. This edge is used when the relationship between
the blocked and target node is known concretely, but does not correspond to an
expansion or a borrow.

Borrow-Flow Edges are labelled with a _Borrow-Flow Edge Kind_ with associated
metadata, enumerated as follows:

### Aggregate

**Metadata**:

- $i_f$: Field Index
- $i_\lifetimeproj$: Lifetime Projection Index

An _aggregate_ kind is used for borrows flowing into an aggregate type (i.e.
struct, tuple). The metadata indicates that the blocked lifetime projection
flows into the ${i_\lifetimeproj}^{th}$ lifetime projection of the ${i_f}^{th}$
field of the blocking lifetime projection.

Introduced in the following two cases:

1. Collapsing an owned place:
   - edges flow from the lifetime projections of the labelled places of the
     base to the lifetime projections of the current base
2. Assigning an aggregate (e.g. `x = Aggregate(a, b)`):
   - edges flow from the lifetime projections of the labelled places in the
     rvalue to the lifetime projections of `x`

<div class="warning">

$i_\lifetimeproj$ is probably not necessary. We probably don't even need $i_f$
for case 1 (field index can be inferred from the expansion place), so perhaps a
different edge kind could be used in that case.

</div>

### Reference to Constant

Connects a region projection from a constant to some PCG node. For example `let
x: &'x C = c;` where `c` is a constant of type `&'c C`, then an edge `{c↓'c} ->
{x↓'x}` of this kind is created. This is called `ConstRef` in the implementation.

<div class="warning">

This seems quite similar to "Borrow Outlives", perhaps we should merge them?

</div>

### Borrow Outlives

For a borrow e.g. `let x: &mut y;`, the PCG analysis inserts edges of this kind
to connect the (potentially snapshotted) lifetime projections of `y` to the
lifetime projections of `x`.

<!-- Concretely:
- For each $\lproj{y}{r}$ of $y$ and $\lproj{x}{r'}$ of $x$:
    - If $r$ outlives $r'$ then:
        - The PCG analysis adds the edge $\{\lproj{y}{r}\} \rightarrow \{\lproj{x}{r'}\}$ -->

### Initial Borrows

To construct the initial PCG state, the PCG analysis adds an edge of this kind
between every lifetime projection in each remote place to the corresponding
lifetime projection of its corresponding argument.

For example, if $\local$ is the local corresponding to a function argument and
contains a lifetime projection $\lproj{\local}{r}$, an edge
$\{\lproj{\remote{\local}}{r}\} \rightarrow \{\lproj{\local}{r}\}$ will appear
in the graph.

Connects the lifetime projections of remote places to the lifetime projections of

### Copy

For a copy `let x = y;`, the PCG analysis inserts edges of this kind
to connect the lifetime projections of `y` to the lifetime projections of `x`.

In the implementation this is currently called `CopyRef`.

### Move

For a move `let x = move y;`, the PCG analysis inserts edges of this kind to
connect the (potentially snapshotted) lifetime projections of `y` to the
lifetime projections of `x`.

### Future

These edges are introduced to describe the flow of borrows to the lifetime
projections of a place that is currently blocked. When they are created, the
target node is a placeholder lifetime projection of a blocked place.

<div class="warning">
Perhaps this should be its own edge type?
</div>

