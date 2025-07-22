# Owned PCG Operations

## Collapse

The operation $\mathit{collapse(p, \Placeexp, \mathcal{C})}$ modifies place
expansions $\Placeexp$ and set of place capabilities $\mathcal{C}$ such that $p$
becomes a leaf in the forest corresponding to $\Placeexp$. Stated more formally
it modifies $\Placeexp$ to ensure that $\Placeexp$ contains an expansion
$\overline{p}$ containing $p$, and $p$ is not the base of any expansion in
$\Placeexp$. Capabilities in $\mathcal{C}$ are updated to account for the
removal of expansions from $\Placeexp$.

*collapse* returns the set of Owned PCG Actions corresponding to the removed
expansions.

<div class="warning">

This logic is very similar to the collapse defined on the (combined) PCG defined
[here](operations/collapse-owned-places.html). This is used in contexts where
the Borrow PCG is not available (such as the join on owned PCGs).

We should investigate making a common operation.

</div>

The algorithm is implemented as follows:

1. Let $\Placeexp'$ be the subset of place expansions in $\Placeexp$ such that
   for each $\overline{p'}$ in $\Placeexp'$, the base place $p'$ is a prefix of
   $p$.
2. Let $\ownedpcgroot''$ be an ordered list of the expansions in
   $\ownedpcgroot'$ sorted in order of descending length of the projections of
   their base place
3. Let $R$ be the list of operations to return
4. For each $\overline{p'}$ in $\ownedpcgroot''$
    1. Let $\overline{c'}$ be the capabilities of $p'$ in $\mathcal{C}$
    2. Let $c$ be the minimum common capabiility of $\overline{c'}$.
    3. Let $p'$ be the base of $\overline{p'}$
    4. Remove capabilities to the places in $\overline{p'}$ from $\mathcal{C}$
    5. Assign capability $c$ to $p'$ in $\mathcal{C}$
    6. Remove $\overline{p'}$ from $\Placeexp$
    7. Add $\texttt{collapse}(p', \overline{p'}, c)$ to $R$
5. return $R$

