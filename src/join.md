# Join Operation

The *join* algorithm on PCGs takes as input PCGs $\pcg$ and $\pcg'$ and
*mutates* $\pcg$ to *join in* $\pcg'$.

<div class="info">

We define the join in this manner because this is similar to how the
implementation works.

</div>

The algorithm proceeds in the follow steps:

1. The Owned PCG of $\pcg'$ is joined into the Owned PCG of $\pcg$ (this may also change the capabilities of $\pcg$)
2. The capabilities of $\pcg'$ are joined into the capabilities of $\pcg$.
3. The Borrow State of $\pcg'$ is joined into the Borrow State of $\pcg$

We now describe each step in detail:

## Owned PCG Join

Let $\ownedpcg$ be the owned PCG of $\pcg$ and $\ownedpcg'$ the PCG of $\pcg'$.

1. For each local $\local$ in the MIR body:
    1. If $v$ is allocated in both $\ownedpcg$ and $\ownedpcg'$:
        1. Join the place expansions rooted at $\ownedpcg'[\local]$ into $\ownedpcg[\local]$
    2. Otherwise, if $v$ is allocated in $\ownedpcg$, it should be deallocated in $\ownedpcg$


### Joining Local Expansions (Algorithm Overview)

The algorithm for joining local expansions also involves modifying capabilities
(including to borrowed places), and also may cause some places to be labelled.
We "emulate" a modification of the block to be joined in, so that we can use the
resulting modified capabilities and borrows graph in the remainder of the join.
We implement the join by defining a "one-way" join operation
$\sqcup^\leftarrow$, and then performing a join $(\pcg,\pcg') \leftarrow \pcg
\sqcup^\leftarrow \pcg'$ and subsequently $(\pcg',\pcg) \rightarrow \pcg'
\sqcup^\leftarrow \pcg$. The owned PCGs of $\pcg$ and $\pcg'$ (including the
associated capabilities) should be the same after the join.  Formally, we could
imagine a partial order $<_\ownedpcg$ where $\pcg_1 <_\pcg \pcg_2$ iff the owned
PCG of $\pcg_1$ can be transformed to the owned PCG of $\pcg_2$ by a sequence of
repack operations on its owned PCG. The join identifies the maximum graph
$\pcg'$ (w.r.t $<_\ownedpcg$) where $\pcg' <_\ownedpcg \pcg_1$ and $\pcg'
<_\ownedpcg \pcg_2$.

Before we present the full algorithm (that takes into account borrows), we first
describe a version that would work in the absence of borrows and therefore only
considers capabilities `W` and `E`. The key point of the join is that all
places/capabilities in the resulting joined PCGs should be obtainable from the
originals (i.e. via a sequence of PCG repacks).
The join starts from the root of both trees, and navigate downwards.  For
expansions that are the same in both, nothing needs to happen.  If the other
tree is expanded more than us, we continue expanding ours: the only reason it
would be expanded is that part of it is moved out, so we can expand and weaken
the LHS to match the RHS. For example, if the LHS is `{x: E}`, and the RHS is
`{x.f: E, x.g: W}`, we'd want to expand `x` in the LHS (note that the subsequent
capability join will properly account for capabilities).

If we're at a place where the expansions differ in both trees (e.g. `x ->
{x@Some}` vs `x -> {x@None}`), we collapse *both* to the place (e.g `x`) and set
capability to the place to W. Neither of the expansion places are accessible by
*both*, so the "most" capability we could obtain is the `W` permission to the base.

More formally, we define the one-way join $join_\leftarrow(\pcg,\pcg')$ as the
traversal where:

1. If we're at a leaf $p$ in $\mathcal{G}$ that is not a leaf in $\mathcal{G'}$
(having children $\overline{p}$), then:
    1. Expand $p$ to $\overline{p}$ in $\mathcal{G}$
2. If were at a node $p$ in $\mathcal{G}$ where the expansion $e$ is not the same as the expansion $e'$ in $\mathcal{G}'$:
    1. Collapse both $\mathcal{G}$ and $\mathcal{G'}$ to $p$ for capability $W$

Now, we extend the join to work with borrows and the read capability $R$.
Borrows complicate the story because it enables mutually exclusive (at runtime)
places to appear in the PCG. For example:

```rust
fn f(x: Either<String, String>) -> &String; {
    let result = match x {
        Left(l) => &l,
        Right(r) => &r
    };
    result
}
```

 After the assignment, we should have $R$ capability to both `x@Left` and
 `x@Right` because they are borrowed into `result`. In the case of exclusive
 borrows, such places would not have capability but still present in the owned
 PCG (again, to reflect the target of `result`). Therefore, the collapse and
 expand rule previously shown are no longer sufficient.

1. If we're at a place $p$ that's a leaf in both $\pcg$ and $\pcg'$:
    1. If $p$ has capability of at least $R$ in $\pcg$ and has capability exactly $R$ in $\pcg'$:
        1. Then, after the join, the place $p$ can have at most capability $R$.
        Its also possible that we can now have incompatible different *owned*
        expansions of $p$ in the joined PCG, that have been borrowed under
        mutually exclusive paths.

<div class="warning">
TODO: continue. (An overly formal version is below)
</div>

#### Local Expansions Join:  $\mathit{join_\ownedpcgroot}$

The algorithm $\mathit{join_\ownedpcgroot}(
    \langle\ownedpcgroot,\mathcal{B},\mathcal{C}\rangle,
    \langle\ownedpcgroot',\mathcal{B}',\mathcal{C}'\rangle
)$
joins a set of place expansions $\ownedpcgroot'$
into a set of place expansions $\ownedpcgroot$, and makes corresponding changes
to borrows $\mathcal{B}$ and capabilities $\mathcal{C}$.

1. If either $\ownedpcgroot$ or $\ownedpcgroot'$ have any expansions:
    1. Perform $\mathit{join_\ownedpcgroot^\leftarrow}(
    \langle\ownedpcgroot,\mathcal{B},\mathcal{C}\rangle,
    \langle\ownedpcgroot',\mathcal{B}',\mathcal{C}'\rangle)$
    2. Perform $\mathit{join_\ownedpcgroot^\leftarrow}(
    \langle\ownedpcgroot',\mathcal{B'},\mathcal{C'}\rangle,
    \langle\ownedpcgroot,\mathcal{B},\mathcal{C}\rangle)$
2. Otherwise:
    1. Let $v$ be the local
    1. Perform $\mathit{join_v^\leftarrow}(
    \langle{}\mathcal{B},\mathcal{C}\rangle,
    \langle{}\mathcal{B}',\mathcal{C}'\rangle)$
    2. Perform $\mathit{join_v^\leftarrow}(
    \langle{}\mathcal{B}',\mathcal{C}'\rangle,
    \langle{}\mathcal{B},\mathcal{C}\rangle)$

We define $\mathit{join_\mathcal{E}^\leftarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}',\mathcal{B}',\mathcal{C}'\rangle)$ as:

1. Let $\overline{p_{collapsed}} = \emptyset$
2. For each expansion $e' \in \mathcal{E}'$ (shortest first):
    1. Let $p'$ be the base of $e'$
    2. If there exists a $p \in \overline{p_{collapsed}}$ where $p$ is a prefix of $p'$, then ignore this expansion
    3. Otherwise, let  $\overline{e}$ by the set of (direct) expansions from $e'$ in $\mathcal{E}$
    4. If $e' \in \overline{e}$:
        1. Perform $\mathit{join_{e'}^\leftarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$
    5. Otherwise, if $\overline{e}$ is empty and $\mathcal{C}[p'] = c$:
        1. If $\mathcal{C'}[p'] = c'$:
            1. Perform $expand^\leftarrow(e',
            \langle{}c, \mathcal{B},\mathcal{C}\rangle,
            \langle{}c', \mathcal{B}',\mathcal{C}'\rangle)$
        2. Otherwise, perform a normal expansion operation of $e'$ in $\mathcal{E}$
    6. Otherwise, perform $\mathit{join_{e'}^\leftrightarrow}( \langle{}\mathcal{E},
    \mathcal{B},\mathcal{C}\rangle, \langle{}\mathcal{E}',
    \mathcal{B}',\mathcal{C}'\rangle)$
        1. If the result of the join is to collapse to $p'$, then add $p'$ to $\overline{p_{collapsed}}$



We define $expand^\leftarrow(e,
\langle{}c, \mathcal{B},\mathcal{C}\rangle,
\langle{}c', \mathcal{B}',\mathcal{C}'\rangle)$ as:

1. If $c \sqcup c' = c''$
    1. Add expansion $e$ to $\mathcal{E}$
    2. Perform $\mathit{join_{e'}^\leftarrow}(
    \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
    \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$
2. Otherwise, if $c = R$:
    1. Let $p$ be the base of $e$
    1. Perform $join_{p_{RW}}^\leftarrow(p, \mathcal{B}, \mathcal{C})$
3. Otherwise do nothing


#### Expansion Edge One-Way Join $join_e^\leftarrow$
We define $\mathit{join_e^\leftarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$ as:

1. For each place $p$ in the expansion of $e$:
    1. Perform $\mathit{join_p^\leftarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$

#### Expansion Edge Two-Way Join $join_e^\leftrightarrow$
We define $\mathit{join_e^\leftrightarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$ as:

1. Let $p$ be the base of $e$
2. If $\mathcal{C}[p] = R$ and $\mathcal{C}'[p] = R$:
    1. Perform a regular expand of $e$
3. Otherwise, if there exists a descendant of $p$ in $\mathcal{E}'$ that does not have a capability:
    1. Insert $e$ into $\mathcal{E}$ (do not change capabilities)
4. Otherwise:
    1. Collapse $\mathcal{E}, \mathcal{C}$ and $\mathcal{E'}, \mathcal{C'}$ to $p$

#### Place Join $join_p^\leftarrow$

We define $\mathit{join_p^\leftarrow}(
        \langle{}\mathcal{E}, \mathcal{B},\mathcal{C}\rangle,
        \langle{}\mathcal{E}', \mathcal{B}',\mathcal{C}'\rangle)$ as:

1. If $p$ is not a leaf in $\mathcal{E}$ or $p$ is not a leaf in $\mathcal{E}'$ or $p \not\in \mathcal{C}$ or $p \not\in \mathcal{C'}$:
    1. Abort
2. Otherwise, let $c = \mathcal{C}[p]$, $c' = \mathcal{C'}[p]$
1. If $c \geqslant R$ and $c' = R$:
    1. Perform $copy_{R}^{\leftarrow}(p, C, C')$
2. If $c = R$ and $c' = W$:
    1. Perform $join_{p_{RW}}^\leftarrow(p, \mathcal{B}, \mathcal{C})$
3. If $c = E$ and $c' = W$:
    1. Perform $copy^{\leftarrow}(p.+, C, C')$

#### Leaf RW Join $join_{p_{RW}}^\leftarrow$

We define $join_{p_{RW}}^\leftarrow(p, \mathcal{B}, \mathcal{C})$ as:
1. Label all postfixes places of $p$ in $\mathcal{B}$
2. $\mathcal{C}[p] = W$

<div class="warning">
TODO: Actually it seems like shared references should maintain E capability even if they're dereferenced
</div>

## Place Capabilitiies Join

The algorithm *join*($\Placecap, \Placecap'$) is defined as:

1. For each `p: c` in $\Placecap$:
    1. If $p \not\in \Placecap'$:
        1. Remove capability to $p$ in $\Placecap$
    2. Otherwise:
        1. If $\mathit{min}(c, \Placecap'[p])$ is defined:
            1. Assign capability $\mathit{min}(c, \Placecap'[p])$ to $p$ in $\Placecap$
        2. Otherwise, remove capability to $p$ in $\Placecap$

## Borrow State Join

1. The borrow graphs are joined
2. The validity conditions are joined

### Borrow PCG Join

Joining $\borrowpcg'$ into $\borrowpcg$, where $\block$ is the block for $\borrowpcg$ and $\block'$ is the block for $\borrowpcg'$.

Update the validity conditions for each edge $e$ in $\borrowpcg'$ to require the
branch condition $b' \rightarrow b$.

Update the validity

1. If $b$ is a loop head perform the loop join algorithm as described [here](./loops.md).
2. Otherwise:
    1. For each edge $e'$ in $\borrowpcg'$:
        1. If there exists an edge $e$ of the same [kind](./definitions/pcg-edges.html#edge-kinds) in $\borrowpcg$
            1. Join the validity conditions associated with $e$ in $\borrowpcg'$ to the validity conditions associated with $e$ in $\borrowpcg$
        2. Otherwise, add $e$ to $\borrowpcg$
    2. For all *placeholder* lifetime projections $\lproj{\pcgplace}{r}~\text{at}~\placeholderlabel$ in $\borrowpcg$:
        1. Label all lifetime projection nodes of the form $\lproj{\pcgplace}{r}$ in $\borrowpcg$ with $\placeholderlabel$
