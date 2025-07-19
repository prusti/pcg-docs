# Repack Operations

Repack operations describe actions on owned places.

## RegainLoanedCapability

**Fields**:
- $p$ - Place
- $c$ - Capability

This operation is used to indicate that $p$ is no longer borrowed, and can
therefore be restored to capability $c$.

<div class="warning">

In principle I think $c$ should always be exclusive capability

</div>

### Applying RegainLoanedCapability
The PCG applies this operation by setting the capability of $p$ to $c$.


## DerefShallowInit

**Fields**:
- $p_f$ - From Place
- $p_t$ - To Place

This operation is used to indicate that a $p_f$ (which is a shallow-initialized
box) was dereferenced.

### Applying DerefShallowInit

Let $\overline{p}$ be the expansion of $p_f$ obtained by expanding towards
$p_t$.

The PCG applies this operation by adding read capability to the places in
$\overline{p}$

<div class="warning">

Why do we use this logic?

</div>

## Collapse
**Fields**:
- $p$ - Place
- $g$ - Collapse Guide
- $c$ - Capability

This operation indicates that the expansion of $p$ should be packed (using guide
$g$) with resulting capability $c$.

### Applying Collapse

Let $\overline{p}$ be the expansion of $p$ towards guide place $g$.


<div style="padding:10px;border:1px solid #FFF">

**Preconditions**:
- Each place $p'$ in $\overline{p}$ has a capability $c_{p'} \geqslant c$

</div>

Let $c'$ be the minimum capability of the places in $\overline{p}$.

- Capability for each place in $\overline{p}$ is removed.
- Capability for $p$ is set to $c'$.
- The Unpack edge from $p$ is removed

<div class="warning">

The current implementation guarantees there is only one unpack edge from $p$. In
the future this may change.

</div>

## Expand
**Fields**:
- $p$ - Place
- $g$ - Expand Guide
- $c$ - Capability

This operation indicates that $p$ should be expanded (using guide $g$) such that
each place in the expansion has capability $c$.

### Applying Expand

Let $\overline{p}$ be the expansion of $p$ towards guide place $g$.


<div style="padding:10px;border:1px solid #FFF">

**Preconditions**:
- $p$ has capability $p_c \geqslant c$

</div>

- The unpack edge $\{p\} \rightarrow \{ \overline{p} \}$ is added
- Capability for every place in $\overline{p}$ is set to $c$
- If $c$ is Read capability, the capability of $p$ is set to Read
- Otherwise, if $c$ is not Read, capability of $p$ is removed

<div class="info">

Note that reference-typed places will never be expanded.

</div>
