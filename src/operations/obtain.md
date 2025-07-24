# Obtaining Capability to a Place

The operation to obtain capability $c$ to a place $p$ in a PCG $\pcg$ proceeds
as follows.

When performing this operation to satisfy the place capability required for a
statement, the analysis guarantees that no live mutable borrows conflicting with
$p$[^rationale]. At a high level, capability to $p$ is obtained by first
collapsing the owned places in $\pcg$ to $p$

[^rationale]: If the program requires capability to the place to do some action,
    then the place cannot be borrowed mutably. This invariant does not hold when
    we are obtaining capability to the place in order to construct a loop
    abstraction.

### Step 1 - Label dereferences of shared borrows stored in $p$

Reborrows of shared references derived from $p$ (i.e. from any postfix of $p$)
will survive even if $p$ is moved or mutated. Therefore, if $c$ permits the
function to mutate $p$ (i.e. $c \neq \readcap$), then the analysis labels all
places that project from shared references derived from $p$.

Formally:

If $c \neq \readcap$, then for each place $p'$ in $\pcg$ where:
- $p'$ is a strict postfix of $p$, and
- $p'$ is a shared reference, and
- $*p'$ is in $\pcg$

The analysis labels every postfix of $p'$ in $\pcg$.

### Step 2 - Collapse

## Implementation

This operation is implemented as [`PlaceObtainer::obtain`](https://github.com/viperproject/pcg/blob/d4591e49f5870b49332d47fcd2a2da1d4678a1a7/src/pcg/visitor/obtain.rs#L778)

The *obtain(p, o)* operation reorganizes a PCG state to a new state in where the
PCG node for a place $p$ is present in the graph. The parameter *o* is an
*Obtain Type* which describes the reason for the expansion. The reason $o$ is either:

- To obtain a specified capability to the place
- To access the place because it is the borrowed place of a two-phase borrow

An *Obtain Type* is associated with a *result capability* $c$ which is either
the specified capability (in the first case), or `Read` (in the case of access
for two-phase borrows).

<div class="warning">

The "two-phase" borrow case is likely unnecessary: we can use the borrow-checker
to detect if the place $p$ is also the borrowed place of a two-phase borrow
reserved at the current location. In fact the current implementation make
similar queries as part of the *expand* step.

</div>

Note that a place node for $p$ is not necessarily present in the graph before
this occurs.

This proceeds as follows:

### Step 1 - Label dereferences of shared borrows stored in $p$

(Same as high-level description)

### Step 2 - Upgrading Closest Ancestor From R to E

This step is included to handle a relatively uncommon case (see the Rationale
section below).

If the *obtain* operation is called with permission $W$ or $E$ and the *closest
ancestor* $p'$ to $p$, that is, the longest prefix of $p$ for which there exists
a node in the graph, has $R$ capability, we upgrade $p'$'s capability to $E$ in
exchange for removing capability to all pre- and postfix places of $p'$ in the
graph (excluding $p'$ itself).

This is sound because if we need to obtain non-read capability to `place`, and
there are any ancestors of `place` in the graph with R capability, one such
ancestor originally had E capability was subsequently downgraded. This function
finds such an ancestor (if one exists), and performs the capability exchange.

<div class="warning">

Perhaps it would be better to explicitly track downgrades in the analysis so
that they can be upgraded later? This will make the soundness argument more
convincing.

</div>

#### Rationale

It's possible that we want to obtain exclusive or write permission to
a field that we currently only have read access for. For example,
consider the following case:

- There is an existing shared borrow of `(*c).f1`
- Therefore we have read permission to *c, (*c).f1, and (*c).f2
- Then, we want to create a mutable borrow of (*c).f2
- This requires obtaining exclusive permission to (*c).f2

We can upgrade capability of (*c).f2 from R to E by downgrading all
other pre-and postfix places of (*c).f2 to None (in this case c and
*c). In the example, (*c).f2 is actually the closest read ancestor,
but this is not always the case (e.g. if we wanted to obtain
(*c).f2.f3 instead)

### Step 3 - Collapse

Then, if a node for $p$ exists in the graph and $p$'s capability is not at least as strong as $c$, *collapse* the subgraph rooted at $p$ (and obtain capability $c$ for $p$) by performing the *collapse(p, c)* operation.

#### *collapse*

The *collapse(p)* operation is implemented as follows:

- For each $p'$ such that $p$ is a [prefix](../definitions/mir.html#place-prefix) of $p'$ (from longest to shortest) and there is a node for $p'$ in the graph:
  - perform the [*Collapse*](./repack-ops.html#Collapse) _Repack Operation_ on $p'$.
  - For each lifetime $'r$ in the type of $p'$:
    - Create a new lifetime projection node $p'\downarrow~'r$
    - For each lifetime projection node $p''\downarrow~'r$ where $p''$ is an expansion of $p'$:
      - Label $p''$
      - Create a new `BorrowFlow` edge $\{p''\downarrow~'r\}\rightarrow\{p'\downarrow~'r\}$

### Step 4 - Labelling $p$
At this point, if $c$ is $W$, we know that a subsequent operation will mutate $p$.
As a result, if there exists a lifetime projection node for $p$ (for example, if $p$ stores a borrow that has since been reborrowed), it will no longer be tied to the current value of $p$.
So, we label $p$ with reason `ReAssign`.

### Step 5 - Expand

At this point there should be a node for some prefix $p'$ of $p$ in the graph such that $\mathcal{C}[p'] \geqslant c$.

We *expand* the graph to $p$ (and obtain the capability for $p$) by performing the *expandTo(p, o)* operation.

#### *expandTo*

The *expandTo* operation is implemented as follows:
- For each [strict prefix](../definitions/mir.html#place-prefix) $p'$ of $p$ (from shortest to longest):
    - If *expanding* $p'$ one level adds new edges to the graph, then
        - We *expand the lifetime projections* of $p'$ one level

The operation to expand a place one level is the *expandPlaceOneLevel* operation, and the operation to expand the lifetime projections one level is *expandLifetimeProjectionsOneLevel*.

#### *expandLifetimeProjectionsOneLevel*

*expandLifetimeProjectionsOneLevel* is defined with three parameters:

- $p_b$: The place to expand
- $e$: The target [expansion](../definitions.html#place-expansion) of $p_b$
- $o$: The Obtain Type

The operation is implemented as follows:

- Let $\overline{p}$ be the expansion of $p_b$ using $e$
- For each lifetime projection $p_b \downarrow r$ of $p_b$:
    - Let $\overline{rp}_r$ be the set of lifetime projections in $\overline{p}$
      with lifetime $r$
    - If $\overline{rp}_r$ is nonempty[^possible]:
        - We identify the base lifetime projection $rp_{b}$ as follows:
            - Let $l$ be the current snapshot location
            - If $o$ is *not* an obtain for capability R:
                - $rp_b = p_b \downarrow r~\texttt{at}~l$
            - Otherwise, if $p_b$ *is blocked by* a two-phase borrow live at $l$:
                - Let $l'$ be the reservation location of the conflicting borrow
                - $rp_b = p_b \downarrow r~\texttt{at}~l'$
            - Otherwise, $rp_b = p_b \downarrow r$
        - Create a new *Borrow PCG Expansion* hyperedge $e = \{rp_b\} \rightarrow \overline{rp}_r$

[^possible]: This could happen e.g. expanding an `x : Option<&'a T>` to a `x@None`
