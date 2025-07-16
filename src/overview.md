# Overview

<div class="warning">
TODO: Clean-up this writing
</div>

The purpose of the *PCG Analysis* is to provide clients with the following:
- The PCG data structure representing the state of ownership and borrowing of Rust
  places at arbitrary [program points](definitions.html#program-point) within a Rust function
- For any pair $pp_i, pp_j$ of consecutive program points, an ordered list of *actions* that describe the transformation of the  PCG of $pp_i$ to the PCG of $pp_j$.

## PCG Analysis Algorithm

The *PCG Analysis Algorithm* operates on the MIR *Body* of a Rust function and
returns a *PCG Analysis* of the function. A *PCG Analysis* contains *PCG Data*
for every reachable[^reachable] MIR location in the Body[^datastorage]. The *PCG
Data* is a tuple of *PCG States* and *PCG Action Data*.

[^reachable]: A MIR location $l$ reachable iff its basic block $b_l$ is
    reachable from the start block in the CFG without traversing *unwind* or
    *fake* edges (the latter kind do not correspond to the actual control flow
    of the function). The original reason for only considering reachable edges
    was to improve performance; removing this constraint (and instead
    considering all locations) would be simple to change in the implementation.

[^datastorage]: The PCG analysis algorithm is implemented as a MIR dataflow
    analysis defined by the rust compiler crate. In the implementation, the PCG
    Data is computed for every reachable MIR location during the algorithm
    execution itself, but only the PCG Data for the entry state of each basic
    block is stored. The PCG Data for an arbitrary location within a block is
    re-computed by applying the dataflow analysis transfer function from the
    entry state.

The *PCG States* of a MIR location is a list of the PCGs computed at that location,
concretely:
- An *Initial* state, followed by
- One state for every [PCG evaluation phase](definitions.html#pcg-evaluation-phase)

The *PCG Action Data* of a MIR location contains a list of *PCG Actions* for
each evaluation phase in the location (i.e. the actions performed at that
phase).

The PCG Analysis Algorithm is implemented as a dataflow analysis in which every
reachable statement is visited exactly once[^confirmimpl]. This property is
ensured because the final state at a loop head is computed upon entering it in
the analysis (without having first seen the body). The join of the state at a
back edge with the state at the loop head should yield the loop head state.

[^confirmimpl]: We should confirm that this also holds in the implementation as this previously was not the case. However, visiting the same stmt multiple times should only affect performance, not correctness.

<div class="warning">
We currently have not implemented the check to join the two states to confirm the correctness of the loop head state.
</div>

## PCG Data Structure

The *PCG* data structure represents the state of ownership and borrowing of Rust
  places at an arbitrary [program point](definitions.html#program-point).

<div class="warning">
Perhaps this describes too much implementation-specific details?
</div>

In our implementation, it consists of three components:
- The *Owned PCG*, which describes the state of [owned places](definitions.html#owned-places)
- The *Borrow State*, which describes borrowed memory (borrowed places and lifetime projections) and borrow relations, and also some auxillary data structures
- The *Place Capabilities* which is a map from places to capabilities

### Owned PCG

The Owned PCG is a forest, where the root of each tree in the forest is a MIR
`Local`. This forest describes how unpacked all of the owned places are. In the
forest, each node is a place, and its child nodes an
[expansion](definitions.html#place-expansion) of the place. The forest can be
viewed as a set of hyper-edges where for each interior node $n$ there is a
hyperedge from the singleton set $\{ n \}$ to its children.

<div class="warning">

Expansions of *borrowed* places are represented as *borrow expansion hyperedges*
in the Borrows Graph. They are used to represent, e.g. the projection $p'$ of a
borrowed place $p$, where $p'$ will be further reborrowed.

It would probably be a better design to remove the Owned PCG and change the
Borrows Graph to a *PCG graph* by changing *borrow expansion* hyperedges to simply be *expansion hyperedges*.

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
thinking about how to implement the *join* operation on the merged data
structure.
</div>

