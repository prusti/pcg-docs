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

It proceeds as follows:

- Until the PCG remains unchanged across the following steps:
    - Let $es$ be the set of edges $e=\{n\}\rightarrow\{n_1, .., n_k\}$ such that either:
      - $e$ is an expanion edge and either:
        - for each $n_i$, either:
          - $n_i = p$ and $isDead(p, l)$, where $l$ is the current snapshot location
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
    - For each $e$ in $es$:
      - TODO 

