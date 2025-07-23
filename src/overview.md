# Overview

The purpose of the _PCG Analysis_ is to provide clients with the following:

- The PCG data structure representing the state of ownership and borrowing of Rust
  places at arbitrary [program points](definitions.html#program-point) within a Rust function
- For any pair $pp_i, pp_j$ of consecutive program points, an ordered list of _actions_ that describe the transformation of the PCG of $pp_i$ to the PCG of $pp_j$.

## PCG Analysis Algorithm

Key Concepts:

- The _PCG Analysis Algorithm_ operates on the MIR _Body_ of a Rust function and
  returns a _PCG Analysis_ of the function.
- A _PCG Analysis_ contains _PCG Data_
  for every reachable[^reachable] MIR location in the Body[^datastorage].
- The _PCG Data_ is a tuple of _PCG States_ and _PCG Action Data_.

[^reachable]:
    A MIR location $l$ reachable iff its basic block $b_l$ is
    reachable from the start block in the CFG without traversing _unwind_ or
    _fake_ edges (the latter kind do not correspond to the actual control flow
    of the function). The original reason for only considering reachable edges
    was to improve performance; removing this constraint (and instead
    considering all locations) would be simple to change in the implementation.

[^datastorage]:
    The PCG analysis algorithm is implemented as a MIR dataflow
    analysis defined by the rust compiler crate. In the implementation, the PCG
    Data is computed for every reachable MIR location during the algorithm
    execution itself, but only the PCG Data for the entry state of each basic
    block is stored. The PCG Data for an arbitrary location within a block is
    re-computed by applying the dataflow analysis transfer function from the
    entry state.

The _PCG States_ of a MIR location is a list of the PCGs computed at that location,
concretely:

- An _Initial_ PCG, followed by
- One PCG for every [PCG evaluation phase](definitions.html#pcg-evaluation-phase)

The _PCG Action Data_ of a MIR location contains a list of _PCG Actions_ for
each evaluation phase in the location (i.e. the actions performed at that
phase).

#### The PCG Dataflow Analysis

The PCG Analysis Algorithm is implemented as a [MIR dataflow
analysis](definitions/mir.html#mir-dataflow-analysis) using `PcgDomainData` as
the domain. `PcgDomainData` contains a `PCGData` value and other relevant
metadata (e.g the associated basic block). Notably, the analysis only analyzes
the statements in each basic block one time. Conceptually, this property is
ensured because the final state at a loop head is computed upon entering it in
the analysis (without having first seen the body).

We note that the behaviour of the *join* operation on `PCGDomainData` requires
tracking of what blocks have been previously joined (this is basically a
consequence of the interface of the MIR dataflow analysis). The `PCGDomainData`
*join* operation joins the PCG $\pcg'$ of block $b'$ *into* the PCG $\pcg$ at
block $b$ as follows:
1. If no block has ever been joined into $b$, then set $\pcg$ = $\pcg'$
2. If the edge from $b'$ to $b$ is *not* a back edge[^backedge] of a loop, then $\pcg'$ is joined into
   $\pcg$ using the algorithm defined [here](./join.md)

[^backedge]: In the join implementation, we an edge from $b'$ to $b$ is a back
    edge if $b$ dominates $b'$ in the CFG

Because the join does not modify the PCG for back edges, the analysis can be
completed without ever having to re-analyse the statements within a block.

<div class="warning">

Our implementation should also be checking that the PCG generated at the loop
head is valid w.r.t the state at the back edge here, but this is not happening
yet.

</div>

## PCG Data Structure

The _PCG_ data structure represents the state of ownership and borrowing of Rust
places at an arbitrary [program point](definitions.html#program-point).

It consists of three components:

- The _Owned PCG_, which describes the state of [owned places](definitions.html#owned-places)
- The _Borrow State_, which describes borrowed memory (borrowed places and lifetime projections) and borrow relations, and also some auxillary data structures
- The _Place Capabilities_ which is a map from places to capabilities

### Owned PCG

The Owned PCG is a forest, where the root of each tree in the forest is a MIR
`Local`.

Each tree in the forest is defined by a set of [place
expansions](./definitions/places.md#place-expansion), which describe how
unpacked all of the owned places are. For each expansion $\overline{p}$ in the
set, the base $p$ is a node in the forest and $\overline{p}$ are its children.
We note that each expansion can be similarly interpreted as a hyperedge $\{p\}
\rightarrow \overline{p}$

Each local in the body of a MIR function is either *unallocated* or *allocated*
in the Owned PCG. A local is allocated iff there exists a corresponding root node
in the Owned PCG, otherwise it is unallocated.

The operation *allocate* $v$ in the Owned PCG requires that $v$ is not
allocated, and adds a new root for $v$. The *deallocate* $v$ operation removes the
forest rooted at $v$.

<!--
<div class="warning">

Expansions of _borrowed_ places are represented as _borrow expansion hyperedges_
in the Borrows Graph. They are used to represent, e.g. the projection $p'$ of a
borrowed place $p$, where $p'$ will be further reborrowed.

It would probably be a better design to remove the Owned PCG and change the
Borrows Graph to a _PCG graph_ by changing _borrow expansion_ hyperedges to simply be _expansion hyperedges_.

This would likely simplify things a bit because algorithms related to
expanding/collapsing are currently defined for both the Owned PCG and the
Borrows Graph. Graph traversal algorithms also become annoying due to the switch at the owned/borrowed boundary.

Furthermore, in contrast to borrow expansion hyperedges, the Owned PCG cannot
represent the expanding a place into multiple enum variants down different
control-flow paths. This information would be useful, e.g. in a borrow that
borrows from different variants depending on the control flow and surviving
after the join. Currently our implementation handles this by redirecting the
borrow to the collapsed place.

However, merging the owned and borrow graphs would probably require a bit of
thinking about how to implement the _join_ operation on the merged data
structure.

</div>
-->

### Borrow State

The Borrow State is a 3-tuple containing a [*Latest Map*](overview/choosing-place-labels.html#the-latest-map) describing the latest locations of each place; a set of [*Validity Conditions*](definitions/validity-conditions.html#validity-conditions) that describes the set of paths leading to the current block; and a *Borrows Graph*, a directed acyclic hypergraph which describes borrowed places, sets of borrows, and their relation to one another.
The *Borrows Graph* is represented as a set of PCG hyperedges.

Because a borrow created within a block exists only for executions that visit that block, we label new borrows using the validity conditions of the block in which they were created.


### Place Capabilities

Place capabilities $\Placecap$ is a partial map from places to capabilities.

<div class="warning">

We may want to change the domain to be maybe-labelled places instead.

</div>
