# Loops

The *loop head* is the basic block with an incoming back edge. We define $l_h$ as the location of the first statement of the loop head.

The *pre-loop* block is the block prior to the loop head. We assume that there is always a unique pre-loop block. The *pre-loop state* $\mathcal{G}_\textit{pre}$ is the state after evaluating the terminator of the pre-loop block.

The following operations are performed when we join the pre-loop block with the loop head. Note that at this point we've already computed $\mathcal{G}_\textit{pre}$.

We construct the state $\mathcal{G}_h$ for the loop head as follows:

### Step 1 - Identify Relevant Loop Places

We identify the following sets of places:

- $P_{live}$: the places used inside the loop that are *[live](definitions.html#place-liveness)* and
  *initialized* at $l_h$.

<div class="TODO">

TODO: Doesn't liveness imply initialization?

</div>

- $\blockedloopplaces$: the subset of $P_{live}$ that are [directly
  borrowed](definitions.html#borrow-liveness) by a borrow [live](definitions.html#borrow-liveness) at $l_h$

- $P_{blockers}$: the subset of $P_{live}$ that contain lifetime projections

- $P_{loop}$: Places used in the loop that may be relevant for the invariant: $\blockedloopplaces \cup P_{blockers}$

$\mathcal{N}_{loop}$ is the union of $P_{loop}$ and the associated lifetime projections of $P_{loop}$.

$RP_{blockers}$ are the associated lifetime projections of $P_{blockers}$.


### Step 2 - Obtain Relevant Loop Nodes in Pre-state Graph

The nodes in $\mathcal{N}_{loop}$ will need to appear in $\mathcal{G}_{h}$ but
may not be present in $\mathcal{G}_{pre}$ (for example, it's possible that the
loop could borrow from a subplace that requires unpacking). We construct a graph
$\mathcal{G}_{pre}'$ by performing the *obtain* operation on each place in
$P_{loop}$.

### Step 3 - Identify Borrow Roots $P_{roots}$

The *borrow roots* of a place $p$ are the most immediate places that $p$
could be borrowing from and later become accessible, and excluding places already
in $P_{loop}$

We defined the borrow roots using the function $roots(p)$:
- Initialize a list $L$ to contain all lifetime projections in $p$
- while $L$ is not empty:
    - Pop $n$ from $L$
    - For each edge $e$ blocked by $n$ in $\mathcal{G}_{pre}'$:
        - If the edge is an unpack edge, add all of its blocked nodes to $L$
        - Otherwise, for each blocked node $n'$ in $e$:
            - If $n' \in \mathcal{N}_{roots}^{p}$ or $n' \in \mathcal{N}_{loop}$, do nothing
            - If $n'$ is live at $l_h$, add $n'$ to $\mathcal{N}_{roots}^{p}$
            - If $n'$ is a root in $\mathcal{G}_{pre}'$, add $n'$ to $\mathcal{N}_{roots}^{p}$
            - Otherwise, add $n'$ to $L$
- The resulting roots are the associated places of $\mathcal{N}_{roots}^{p}$

We then identify $P_{roots}$, the most immediate nodes that $P_{loop}$ could be
borrowing from and later become accessible (excluding nodes already in
$\mathcal{P}_{loop}$). $P_{roots}$ is the union of the roots for each place in
$P_{loop}$.

### Step 4 - Construct Abstraction Graph And Compute Blocked Lifetime Projections
We construct an abstraction graph $\mathcal{A}$ that describes the blocking
relations potentially introduced in the loop from places in
$P_\textit{roots}$ to nodes in $P_{blockers}$ and from nodes in
$\blockedloopplaces$ to nodes in $P_{blockers}$.

#### *connect()* function:
We begin by define a helper function $connect(p_{blocked}, p_{blocker})$ which adds edges to $\mathcal{A}$ based on $p_{blocked}$ being blocked by $p_{blocker}$ in the loop:
- Identify $p_{blocker} \downarrow r_{top}$: the top-level lifetime projection in $p_{blocker}$
    - Insert a loop abstraction edge $\{p_{blocked}\} \rightarrow \{p_{blocker} \downarrow~r_{top}\}$ into $\mathcal{A}$
- For each $p_{blocked} \downarrow r \in RP(p_{blocked})$:
    - Identify the lifetime projections in $p_{blocker}$ that may mutate borrows in $p_{blocked} \downarrow r$
        - $RP_{mut} = \{p \downarrow r'~|~ p \downarrow r' \in RP(p_{blocker}), r \approx r'\}$
        - If $RP_{mut}$ is nonempty:
            - Introduce a placeholder node $p_{blocked} \downarrow r~\mathtt{at~FUTURE}$
            - Add a borrowflow hyperedge $\{p_{blocked} \downarrow r \} \rightarrow RP_{mut}$
            - Add a future hyperedges:
                - $\{p_{blocked} \downarrow r\} \rightarrow \{p_{blocked} \downarrow r~\mathtt{at~FUTURE}\}$
                - $RP_{mut} \rightarrow \{p_{blocked} \downarrow r~\mathtt{at~FUTURE}\}$
    - Identify the lifetime projections in $p_{blocker}$ that borrows in $p_{blocked} \downarrow r$ may flow into
        - $RP_{flow} = \{p \downarrow r'~|~ p \downarrow r' \in RP(p_{blocker}), r~\text{outlives}~r'\} \setminus RP_{flow}$
        - If $RP_{flow}$ is nonempty:
            - Add a borrowflow hyperedge $\{p_{blocked} \downarrow r \} \rightarrow RP_{flow}$

#### Algorithm:

- For each blocker place $p_{blocker} \in P_{blocker}$:
    - For each $p_{blocked} \in (P_{roots} \cup P_{blocked})$:
        - If $p_{blocked}$ is a remote node, or if $p_{blocker}$ blocks $p_{root}$ at $l_h$:
            - Perform $connect(p_{blocked}, p_{blocker})$

-  Subsequently, ensure that $\mathcal{A}$ is well-formed by adding unpack edges where appropriate. For example, if `(*x).f` is in the graph, there should also be an expansion edge from `*x` to `(*x).f`.
- We identify the set $RP_{rename}$ of lifetime projections that will need to be renamed (indicating they will be expanded in the loop and remain non-accessible at the loop head). $RP_{rename}$ is the set of non-leaf lifetime projection nodes in $\mathcal{A}$ (leaf nodes are accessible at the head).
- Label all lifetime projections in $RP_{rename}$ with location $l_h$, add connections to their `Future` nodes as necessary.

### Step 5 - Label Blocked Lifetime Projections in Pre-State
The resulting graph for the loop head will require new labels on lifetime projections modified in the loop. We begin by constructing an intermediate  graph $\mathcal{G}_{pre}''$  by labelling each lifetime projection in $RP_{rename}$ with $l_h$ and remove capabilities to all places in $P_{remove}$ in $\mathcal{G}_{pre}'$.

### Step 6 - Identify Pre-State Subgraph to Replace With Abstraction Graph
We then identify the subgraph $\mathcal{G}_{cut} \subseteq \mathcal{G}_{pre}''$ that will be removed from $\mathcal{G}_{pre}''$ and replaced with the loop abstraction $\mathcal{A}$.
- Let $\mathcal{N}_{cut}$ = $nodes(\mathcal{A})$.
- We construct $\mathcal{G}_{cut}$ by including all nodes in $\mathcal{N}_{cut}$ and all edges $e$ where there exists $n, n' \in \mathcal{N}_{cut}$ where $e$ is on a path between $n$ and $n'$ in $\mathcal{G}_\textit{pre}''$.

### Step 7 - Replace Pre-State Subgraph with Abstraction Graph
The graph $\mathcal{G_h}$ for the loop head is defined as $\mathcal{G_h} = \mathcal{G}_{pre}'' \setminus \mathcal{G}_{cut} \cup \mathcal{A}$

### Step 8 (Optional) - Confirm Invariant is Correct
To confirm that the resulting graph is correct, for any back edge into the state at $\mathcal{G}_h$ with state $\mathcal{G}'$, performing the *loop join* operation on $\mathcal{G}'$ and $\mathcal{G}_h$ should yield $\mathcal{G}_h$.

[^note]: If the edge is a deref expansion, only add the blocked lifetime projection
[^live]: The liveness condition could also be checked for the block after the loop (assuming there is a single block). However the result is equivalent: if any node is live at $l_h$ but not after the loop, then it must be used inside the loop, and should be part of $\mathcal{N}_{loop}$ and therefore not in $\mathcal{N}_{roots}$.
