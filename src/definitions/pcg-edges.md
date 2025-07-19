# PCG Hyperedges

A PCG Hyperedge is a directed edge of the form $\overline{n_s} \rightarrow
\overline{n_t}$, where elements of $\overline{n_s}$ and $\overline{n_t}$ are PCG
nodes. The set $\overline{n_s}$ are referred to as the *blocked nodes* of the
edge, and $\overline{n_t}$ are the *blocking ndoes*. Hyperedges in the PCG are
labelled with [validity conditions](./validity-conditions.md)[^owned].

[^owned]: Currently not in the owned portion of the PCG, but this should happen eventually.

We currently define the following edge types:

## Unpack Edges

Unpack edges are used to represent the unpack of an *owned* place in order to
access one of its fields. For example, writing to a field `x.f` requires
expanding `x`.

An unpack edge connects an *owned* place $p$ to one of it's
[expansions](./places.html#place-expansion) $\overline{p}$.
Each place in $\overline{p}$ is guaranteed to be owned.

For example, if `x` is an owned place with fields `x.f` and `x.g`, the edge
`{x} -> {x.f, x.g}` is a valid unpack edge.

Unpack edges are *not* generated for dereferences of reference-typed places.
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
- *Dereference Expansion*: The dereference of a reference-typed place
- *Place Expansion*: The expansion of a borrowed place to access one of its fields
- *Lifetime Projection Expansion*: The expansion of the lifetime projections of an owned or borrowed place

### Dereference Expansion

The *blocked nodes* of a dereference expansion consist of:
- A *maybe-labelled* place $\maybelabelled_s$, and:
- A lifetime projection $\lifetimeproj_s$

Where $\maybelabelled_s$ and $\lifetimeproj_s$ have the same associated place $p_s$.

The *blocking node* $\maybelabelled_t$ of a dereference expansion is a
maybe-labelled place with associated place $*p_s$.

### Place Expansion

The *blocked node* of a place expansion is a maybe-labelled place
$\maybelabelled_s$ with associated place $p_s$, where $p_s$ is a borrowed place
and $p_s$ is not a reference.

The *blocking nodes* of a place expansion is a set of maybe-labelled places
$\overline{\maybelabelled_t}$ where the associated places of
$\overline{\maybelabelled_t}$ are an expansion of $p_s$.

### Lifetime Projection Expansion

The *blocked node* of a lifetime projection expansion is a lifetime projection
$\lifetimeproj_s$ where $\base(\lifetimeproj_s)$ is a maybe-labelled place $\maybelabelled_s$ with associated place of $p_s$.

The *blocking nodes* of a lifetime projection expansion is a set of lifetime
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

- *Local Borrow Edges*: A borrow created in the MIR Body,
  e.g. from a statement `let y = &mut x;`
- *Remote Borrow Edges*: A borrow created by the *caller* of this function where the assigned place of the borrow is an input to this function.

Remote Borrows are named as such because (unlike local borrows), the borrowed
place does not have a name in the MIR body (since it was created by the caller).

### Local Borrows

The *blocked node* of a local borrow is a maybe-labelled place $\maybelabelled$.
The *blocking node* of a local borrow is a lifetime projection $\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.


### Remote Borrows

The *blocked node* of a remote borrow is a remote place $\remote{\local}$.
The *blocking node* of a remote borrow is a lifetime projection $\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

## Abstraction Edge

An abstraction edge represents the flow of borrows introduced due to a function
call or loop.

### Function Call Abstraction Edge

The *blocked node* of a function call abstraction edge is a lifetime projection
$\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.

The *blocking node* of a function call abstraction edge is a lifetime projection
$\lifetimeproj$ where $\base(\lifetimeproj)$ is a maybe-labelled place.


### Loop Abstraction Edge

The *blocked node* of a loop abstraction edge is a PCG node.

The *blocking node* of a loop abstraction edge is a [local PCG
node](pcg-nodes.html#local-pcg-nodes).

## Borrow-Flow Edge

A borrow-flow edge represents the flow of borrows between a lifetime projection
$\lifetimeproj_s$ and a [local](pcg-nodes.html#local-pcg-nodes) lifetime
projection $\lifetimeproj_t$. This edge is used when the relationship between
the blocked and blocking node is known concretely, but does not correspond to an
expansion or a borrow.

Borrow-Flow Edges are labelled with a *Borrow-Flow Edge Kind* with associated
metadata, enumerated as follows:

### Aggregate

**Metadata**:
- $i_f$: Field Index
- $i_\lifetimeproj$: Lifetime Projection Index

An *aggregate* kind is used for borrows flowing into an aggregate type (i.e.
struct, tuple). The metadata indicates that the blocked lifetime projection
flows into the $i_\lifetimeproj$'th
