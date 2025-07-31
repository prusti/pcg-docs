# Borrow PCG Actions

## LabelLifetimeProjection

**Fields**
- *predicate* - A predicate describing lifetime projections that should be labelled
- *label* - The label to apply (`current`, `FUTURE` or a label $\label$)

### Applying LabelLifetimeProjection

Replaces the label associated with lifetime projections in the borrow PCG
matching *predicate*. If *label* is `current`, then the label of each matching
lifetime projection is removed.

## Weaken

**Fields**:
- $p$ - Place
- $c_f$ - From capability
- $c_t$ - (Optional) To capability

Used to reduce the capability of a place.
In general the $c_f$ is Exclusive, for example in the following cases:

- Before writing to $p$, capability should be reduced to Write
- When a two-phase borrow is activated, capabilities to places conflicting with
  the borrowed place should be removed

### Applying Weaken

If $c_t$ is defined, the capability of $p$ is set to $c_t$. Otherwise,
capability to $p$ is removed.

## RestoreCapability

**Fields**:
- $p$ - Place
- $c$ - Capability

Instructs that the capability to the place should be restored to the given
capability, e.g. after a borrow expires, the borrowed place should be restored
to exclusive capability.

### Applying RestoreCapability

The capability of $p$ is set to $c$.

## LabelPlace

**Fields**
- $p$ - Place
- $s$ - The snapshot location to use
- *reason* - Why the place is to be made labelled

The purpose of this action is to label current versions of $p$ (and potentially
prefixes and postfixes of $p$) with the label corresponding to the last time
they were updated.

There are six reasons defined:
- `StorageDead`
- `MoveOut`
- `ReAssign`
- `LabelSharedDerefProjections`
- `Collapse`

### Applying LabelPlace


The behaviour of this action depends on *reason*:

#### `ReAssign`, `StorageDead`, `MoveOut`

The places to be labelled are:
- All postfixes of $p$
- All prefixes of $p$ *prior* to the first dereference of a reference.

For example, if $p$ is `(*x).f`, then `*((*x).f)`, `(*x).f`, and `*x` will be
labelled.

### `Collapse`

The place $p$ is labelled (but none of its prefixes or postfixes).

### `LabelSharedDerefProjections`

All *strict* postfixes of $p$ are labelled.

## RemoveEdge

Removes an edge from the graph. If the removal of the edge causes any place
nodes to be removed from the graph, the capability of those places are removed.

## AddEdge

Inserts an edge into the graph. This does not change the capabilities.
