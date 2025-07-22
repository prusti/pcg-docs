# Analysing Statements

The PCG Analysis computes four states for each MIR statement, corresponding to the [PCG evaluation phases](./definitions.html?#pcg-evaluation-phase):

- `PreOperands`
- `PostOperands`
- `PreMain`
- `PostMain`

The analysis for each statement proceeds in two steps:

- Step 1: *Place Conditions* are computed for each statement phase
- Step 2: *PCG Actions* are performed for each statement phase

## Determining Place Conditions

A *place condition* is a predicate on the PCG related to a particular MIR place.

We define the following place conditions:

- `Capability`: Place $p$ must have capability $c$
- `RemoveCapability`: Capability for place $p$ should be removed[^removecap]
- `AllocateOrDeallocate`: Storage for local $\local$ is allocated (e.g. via the `StorageLive` instruction)
- `Unalloc`: Storage for local $\local$ is not allocated (e.g. via the `StorageDead` instruction)
- `ExpandTwoPhase`: Place $p$ is the borrowed place of a two-phase borrow
- `Return`: The `RETURN` place has Exclusive capability

[^removecap]: This is only used for mutably borrowed places

<div class="warning">

`ExpandTwoPhase` may not be necessary. `AllocateOrDeallocate` is a confusing
name, also it's not clear if it's any different than just having Write
permission.

</div>

During this step of the analysis, place conditions are computed for each phase.
The determination of place conditions is based on the MIR statement; the state
of the PCG is not relevant.

The conditions computed for each phase are as follows:

- `PreOperands`: Pre-conditions on the PCG for the operands in the statement to be evaluated
- `PostOperands`: Post-conditions on the PCG after the operands in the statement has been evaluated
- `PreMain`: Pre-conditions on the PCG for the main effect of the statement to be applied
- `PostMain`: Post-conditions on the PCG after the main effect of the statement has been applied

As an example, the MIR statement: `let y = move x` would have the following
place conditions:

- `PreOperands`: `{x: E}`
- `PostOperands`: `{x: W}`
- `PreMain`: `{y: W}`
- `PostMain`: `{y: E}`


The rules describing how these place conditions are generated for a statement
are described [here](./statements/place-condition-rules.md).

## Performing PCG Actions

After the place conditions for each phase are computed, the analyses proceeds by
performing the actions for each phase. At a high-level, this proceeds as follows:

### `PreOperands`

1. The Borrow PCG graph is *minimized* by repeatedly removing every *effective
leaf edge*[^effective] $e$ for which their target PCG nodes of $e$ are not live
at the current MIR location. A Borrow PCG `RemoveEdge` action is generated for
each removed edge. See more details
[here](../operations/pack-old-and-dead-borrow-leaves.html).

<div class="warning">

TODO: Precisely define liveness.

</div>

2. The place capabilities required by the `PreOperand` place conditions are
   [obtained](../operations/obtain.html).

### `PostOperands`

No actions occur at this stage.
Capabilities for every moved-out operand are set to Write.

### `PreMain`

The place capabilities required by the `PreMain` place conditions are
[obtained](../operations/obtain.html).

Then, the behaviour depends on the type of statement:

1. `StorageDead(v)`
   1. The analysis performs the `MakePlaceOld(v, StorageDead)` action.
2. `Assign(p r)`
   1. If `p` is a reference-typed value and contained in the borrows graph and the capability for `p` is `R`:
      1. The analysis performs the `RestoreCapability(p, E)` action
   2. If $\mathcal{C}[p] \neq \texttt{W}$:
      1. The analysis performs the $\texttt{Weaken}(p, \mathcal{C}[p], \texttt{W})$ action
   3. All edges in the borrow PCG blocked by any of the lifetime projections in
      `p` are removed


### `PostMain`

1. For every operand `move p` in the statement:
   1. The analysis performs the `MakePlaceOld(p, MoveOut)` action.
2. If the statement is a function call `p = call f(..)`:
   1. The entry for `p` in the *latest* map is updated to the current location
   2. Function call abstraction edges are described using the rules defined [here](./function-calls.md)
3. If the statement takes the form `Assign(p, r)`:
   1. The entry for `p` in the *latest* map is updated to the current location
   2. `p` is given exclusive permission
   3. If $r$ takes the form `Aggregate(o_1, ..., o_n)`:
      1. For every $i, 0 \leqslant i < n$:

<div class="warning">
TODO: Explain more
</div>

[^effective]: The set of *effective leaf edges* are the leaf edges in the graph
    obtained by removing all edges to placeholder lifetime projections.
