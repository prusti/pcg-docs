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

The algorithm $\mathit{join_\ownedpcgroot}(\ownedpcgroot, \ownedpcgroot', \mathcal{C}, \mathcal{C}')$ joins a set of place expansions $\ownedpcgroot'$ into a set of place expansions $\ownedpcgroot$, and makes corresponding changes to capabilities $\mathcal{C}$.

1. Let $\ownedpcgroot''$ be an ordered list of the expansions in $\ownedpcgroot'$ sorted in order of ascending length of the projections of their base place
2. For each $\overline{p'}$ in $\ownedpcgroot''$:
    1. Let $p'$ be the base of $\overline{p'}$.
    2. If there exists a $\overline{p} \in \ownedpcgroot$ where the base of $\overline{p}$ is $p'$:
        1. If $\overline{p} \neq \overline{p'}$
            1. Perform [collapse](./owned-pcg-operations.md/#collapse)($p'$, $\ownedpcgroot$, $\mathcal{C}$)
            2. Otherwise do nothing (go back to the top of the loop)
    3. Otherwise, if $\ownedpcgroot$ contains an expansion $\overline{p}$ and
       $p' \in \overline{p}$:
       1. Add $\overline{p'}$ to $\ownedpcgroot$
       2. If $p' \in \mathcal{C}'$:
            1. Assign capability $\mathcal{C}'[p']$ to $p'$ in $\mathcal{C}$
            2. Otherwise, remove capability to $p'$ in $\mathcal{C}$
       3. For each $p'' \in \overline{p'}$:
            1. If $p'' \in \mathcal{C}'$:
                1. Assign capability $\mathcal{C}'[p'']$ to $p''$ in $\mathcal{C}$
            2. Otherwise, remove capability to $p''$ in $\mathcal{C}$

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
