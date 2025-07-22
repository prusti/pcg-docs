# Packing Old and Dead Borrow Leaves

The *packOldAndDeadBorrowLeaves* operation removes leaf nodes in the _Borrow PCG_ that are old or dead (according to the borrow checker).

- $l$: the current MIR location

When analysing a particular location, this operation is performed before the effect of the statement.

Note that the liveness calculation is performed based on what happened at the end of the *previous* statement.
    
For example when evaluating:
```
bb0[1]: let x = &mut y;
bb0[2]: *x = 2;
bb0[3]: ... // x is dead
```

we do not remove the `*x -> y` edge until `bb0[3]`.
This ensures that the edge appears in the graph at the end of `bb0[2]` (rather than never at all).
    
This operation is implemented as `PcgVisitor::pack_old_and_dead_borrow_leaves` (see [https://github.com/viperproject/pcg/blob/main/src/pcg/visitor/pack.rs](https://github.com/viperproject/pcg/blob/main/src/pcg/visitor/pack.rs)

We must first introduce some auxiliary operations:

#### *isDead*

*isDead(n, l)* is true if and only if the borrow checker considers the node $n$ to be dead at MIR location $l.$

#### *removeEdgeAndPerformAssociatedStateUpdates*
<!-- we assume that during_cleanup is true -->

*removeEdgeAndPerformAssociatedStateUpdates* is defined with one parameter:

- $e$: the edge to remove

It proceeds as follows: 

- For each current place node $p$ that would be unblocked by removing $e$:
  - If $p$ does not have $R$ capability, and $p$ is mutable:
    - Update $\mathcal{L}$ to map $p$ to $\texttt{after}~l$ where $l$ is the current MIR location
- Remove $e$ from the graph
- For each current place node $p$ that is unblocked by removing $e$:
  - Let $c$ be $R$ if $p$ projects a shared reference and $E$ otherwise
  - If $p$ has no capability or $\texttt{e}$ capability, upgrade its capability to $c$
  - Unlabel each region projection of $p$
- If $e$ is a *Borrow PCG Expansion* edge:
  - If $e$ is a *Dereference Expansion* $\{\tilde{p_s}, rp_s\}\rightarrow p_t$ where $p_t$ is a current place with no lifetime projections:
    - unlabel $rp_s$
  - If $e$ has a source node $p_s$ where $p_s$ is a current place:
    - For each place node $p_t$ in the expansion of $e$, label each region projection of $p_t$ with $\texttt{prepare}~l$, where $l$ is the current MIR location
- If $E$ is a *Borrow* edge; $isDead(e, l)$ where $l$ is the current MIR location; the target of the borrow is a current place $p$; and $p$ has non-zero capability:
  - weaken $p$'s capability to $W$

### Main Loop

*packOldAndDeadBorrowLeaves* proceeds as follows:
<!-- Note: this has not been updated to match the version with the additional `for_place` parameter -->

- Until the PCG remains unchanged across the following steps:
    - Let $E$ be be the set of edges $e = \{n\}\rightarrow\{n_1, .., n_k\}$ such that either:
      - $e$ is an *Borrow PCG Expansion* edge and either:
        - for each $n_i$, either:
          - $n_i = p$ and $isDead(p, l)$, where $l$ is the current MIR location
          - or $n_i$ is old
        - or $n = p$, any pair of place nodes in $\{n_1, .., n_k\}$ have the same capability, and for all $n_i$ such that $n_i = p_i$, $p_i$ has the same label as $p$ and $p$ is an exact prefix of $p_i$
        - or $n = p\downarrow~'r$ and for all $n_i$ such that $n_i = p_i \downarrow~'r_i$, $p$ is an exact prefix of $p_i$, $p$ and $p_i$ have the same label, and $'r$ and $'r_i$ have the same label.
      - or each $n_i$ is not a local, and either:
        - $n_i = p$ and either:
        - $p$ is old
        - or $p$ has a non-empty projection and $n_i$ *is not blocked by* an edge
        - or $n_i = p_i\downarrow~'r_i$ and either:
        - $p_i$ is old
        - or $p_i$ has a non-empty projection and $n_i$ *is not blocked by* an edge
    - For each $e$ in $E$:
      - perform *removeEdgeAndPerformAssociatedStateUpdates(e)*
