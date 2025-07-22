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

*isDead(n, l)* is true if and only if the borrow checker considers the node $n$ to be dead at MIR location $l$.

#### *removeEdgeAndPerformAssociatedStateUpdates*

*removeEdgeAndPerformAssociatedStateUpdates* is defined with one parameter:

- $e$: the edge to remove

It proceeds as follows: 

- TODO update latest?
- Remove $e$ from the graph
- Let $N$ be the subset of the nodes blocked by $e$ which have no blocking edges in the current graph. For each $n \in N$:
  - If $n$ is an unlabeled place $p$: 
    - Let $c$ be $R$ if $p$ projects a shared reference and $E$ otherwise
    - If $p$ has no capability, upgrade its capability to $c$
    - Unlabel each region projection of $p$
- If $e$ is an `Unpack` edge:
  - If $e = \{p_s\downarrow~'r_s\}\rightarrow~\{\overline{p_t\downarrow~'r_t}\}$ and $p_s$ is an owned place:
    - Let $E$ be the set of edges blocked by some $p_t\downarrow~'r_t$
    - Change the target of each edge in $E$ to $p_s\downarrow~'r_s$
    - If ... deref\_blocked\_place (TODO)
    - For each place node $p$ in the expansion of $e$, label each region projection of $p$ 
- If $E$ is a `Borrow` edge, $isDead(e, l)$, where $l$ is the current snapshot location, the target of the borrow is an unlabeled place $p$, and $p$ has some capability:
  - 

### Main Loop

*packOldAndDeadBorrowLeaves* proceeds as follows:

- Until the PCG remains unchanged across the following steps:
    - Let $E$ be be the set of edges $e = \{n\}\rightarrow\{n_1, .., n_k\}$ such that either:
      - $e$ is an `Unpack` edge and either:
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
    - For each $e$ in $E$:
      - perform *removeEdgeAndPerformAssociatedStateUpdates(e)*
