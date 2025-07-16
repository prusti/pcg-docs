# Overview

<div class="warning">
TODO: Clean-up this writing
</div>

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
each basic block one time. Conceptually, this property is ensured because the
final state at a loop head is computed upon entering it in the analysis (without
having first seen the body).

We note that the behaviour of the *join* operation on `PCGDomainData` requires
careful tracking of what blocks have been previously joined (this is basically a
consequence of the interface of the MIR dataflow analysis). We define
$\mathit{join}(s', s)$ (joining the state computed at $s$ into $s'$) as follows:
- Let $b', b$ be the associated blocks of $s'$ and $s$ respectively

In the implementation the *join* operation
associated with the `PcgDomainData`, we have $\mathit{join}(s_h, s_b) = s_h$ if $s_h$
is the state of a loop head and $s_b$ is the state of a back edge; this ensures
that loop heads are only considered once[^confirmimpl].

[^confirmimpl]: We should confirm that this also holds in the implementation as this previously was not the case. However, visiting the same stmt multiple times should only affect performance, not correctness.

<div class="warning">
Our implementation should also be checking that the PCG generated at the loop head is valid w.r.t the state at the back edge here, but this is not happening yet.
</div>

We note that to correspond

## PCG Data Structure

The _PCG_ data structure represents the state of ownership and borrowing of Rust
places at an arbitrary [program point](definitions.html#program-point).

<div class="warning">
Perhaps this describes too much implementation-specific details?
</div>

In our implementation, it consists of three components:

- The _Owned PCG_, which describes the state of [owned places](definitions.html#owned-places)
- The _Borrow State_, which describes borrowed memory (borrowed places and lifetime projections) and borrow relations, and also some auxillary data structures
- The _Place Capabilities_ which is a map from places to capabilities

### Owned PCG

The Owned PCG is a forest, where the root of each tree in the forest is a MIR
`Local`. This forest describes how unpacked all of the owned places are. In the
forest, each node is a place, and its child nodes an
[expansion](definitions.html#place-expansion) of the place. The forest can be
viewed as a set of hyper-edges where for each interior node $n$ there is a
hyperedge from the singleton set $\{ n \}$ to its children.

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
