# Loops

The *loop head* is the basic block with an incoming back edge. We define $l_h$ as the location of the first statement of the loop head.

The *pre-loop* block is the block prior to the loop head. We assume that there is always a unique pre-loop block. The *pre-loop state* $\mathcal{G}_\textit{pre}$ is the state after evaluating the terminator of the pre-loop block.

The following operations are performed when we join the pre-loop block with the loop head. Note that at this point we've already computed $\mathcal{G}_\textit{pre}$.

We construct the state $\mathcal{G}_h$ for the loop head as follows:

### Step 1 - Identify Relevant Loop Nodes

<!-- In this step we identify $\mathcal{N}_{blocked}$ and $RP_{blocker}$, the sets of
PCG nodes used inside the loop that may potentially be included in the loop invariants. -->
We identify the following sets of nodes:

- $P_{loop}$: the places used inside the loop that are *live* and *initialized* at $l_h$.

- $RP_{blocker}$: the set of associated lifetime projections of $P_{loop}$.

- $P_{blocked}$: the subset of $P_{loop}$ that are directly borrowed at $l_h$ by a borrow live at $l_h$[^borrow-live].

- $N_{blocked}$: the union of $P_{blocked}$ and associated lifetime projections

- $\mathcal{N}_{loop}$: $RP_{blocker} \cup \mathcal{N}_{blocked}$.
[^borrow-live]: A live borrow is one for which the loan has definitely not been killed by $l_h$.

### Step 2 - Expand Pre-State Graph to Include Relevant Loop Nodes
The places in $\mathcal{N}_{loop}$ will need to appear in $\mathcal{G}_{h}$ but may not be present in $\mathcal{G}_{pre}$ (for example, it's possible that the loop could borrow from a subplace that requires unpacking). We construct a graph $\mathcal{G}_{pre}'$ by unpacking $\mathcal{G}_{pre}$ such that $\mathcal{G}_{pre}'$ contains all places in $\mathcal{N}_{loop}$.[^nofail]

### Step 3 - Identify Root Nodes
We then identify $\mathcal{N}_{roots}$, the most immediate nodes that $\mathcal{N}_{loop}$ could be borrowing from and later become accessible (excluding nodes already in $\mathcal{N}_{loop})$. Note that unlike the method for deriving $\mathcal{N}_{loop}$, identifying these nodes requires considering the PCG state $\mathcal{G}_{pre}'$.
<br/>The algorithm to compute $\mathcal{N}_{roots}$ is:
- Initialize $\mathcal{N}_{roots} = \emptyset$
- For each $n_{loop} \in \mathcal{N}_{loop}$:
    - Initialize a list $L = [n_{loop}]$
    - while $L$ is not empty:
        - Pop $n$ from $L$
        - For each edge $e$ blocked by $n$ in $\mathcal{G}_{pre}'$:
            - If the edge is an unpack edge, add all of its blocked nodes to $L$[^note]
            - Otherwise, for each blocked node $n'$ in $e$:
                - If $n' \in \mathcal{N}_{roots}$ or $n' \in \mathcal{N}_{loop}$, do nothing
                - If $n'$ is live at $l_h$, add $n'$ to $\mathcal{N}_{roots}$[^live]
                - If $n'$ is a root in $\mathcal{G}_{pre}'$, add $n'$ to $\mathcal{N}_{roots}$
                - Otherwise, add $n'$ to $L$

### Step 4 - Construct Abstraction Graph
We construct an abstraction graph $\mathcal{A}$ that describes the blocking
relations potentially introduced in the loop from nodes in
$\mathcal{N}_\textit{roots}$ to nodes in $RP_{blockers}$ and from nodes in
$\mathcal{N}_{blocked}$ to nodes in $RP_{blockers}$.
In the process we also identify:
- $RP_{rename}$: the lifetime projections that will need to be re-labelled in $\mathcal{G}_{h}$

**Algorithm**:

- For each candidate *blocked place* $p_{blocked}$ in $\mathcal{N}_{blocked}
  \cup \mathcal{N}_{roots}$:
    - The set of *blockers* $RP_b$ is the subset of $RP_{blocked}$ such that each $p_{blocker} \downarrow r$ in $RP_b$:
        - $p_{blocker}$ and $p_{blocked}$ have distinct related locals
        - $p_{blocker} \downarrow r$ [blocks](./definitions.html#blocking) $p_{blocked}$ at $l_h$.
    - For each $p_{blocker} \downarrow r \in RP_b$:
        - Insert a loop abstraction edge $\{p_{blocked}\} \rightarrow \{p \downarrow~r\}$ into $\mathcal{A}$
        - For each lifetime projection $p_{blocked} \downarrow r'$ in $p_{blocked}$:
            - Insert a loop abstraction edge $\{p_{blocked}\} \rightarrow \{p \downarrow~r\}$ into $\mathcal{A}$
            - Identify $RP_{mut}$: the subset of lifetime projections in $p_{blocker}$ that may mutate borrows in $p_{blocked}$
                - $RP_{mut} = \{p \downarrow r''~|~ p \downarrow r'' \in RP(p_{blocker}), r' \approx r''\}$
            - If $RP_{mut}$ is nonempty:
                - Introduce a placeholder node $p_{blocked} \downarrow r'~\mathtt{at~FUTURE}$
-  Subsequently, ensure that $\mathcal{A}$ is well-formed by adding unpack edges where appropriate. For example, if `(*x).f` is in the graph, there should also be an expansion edge from `*x` to `(*x).f`.
- We identify the set $RP_{rename}$ of lifetime projections that will need to be renamed (indicating they will be expanded in the loop and remain non-accessible at the loop head). $RP_{rename}$ is the set of non-leaf lifetime projection nodes in $\mathcal{A}$ (leaf nodes are accessible at the head).
- Label all lifetime projections in $RP_{rename}$ with location $l_h$, add connections to their `Future` nodes as necessary.

### Step 5 - Label Affected Lifetime Projections in Pre-State
The resulting graph for the loop head will require new labels on lifetime projections modified in the loop. We begin by constructing an intermediate  graph $\mathcal{G}_{pre}''$  by labelling each lifetime projection in $RP_{rename}$ with $l_h$ and remove capabilities to all places in $P_{remove}$ in $\mathcal{G}_{pre}'$.

### Step 6 - Identify Pre-State Subgraph to Replace With Abstraction Graph
We then identify the subgraph $\mathcal{G}_{cut} \subseteq \mathcal{G}_{pre}''$ that will be removed from $\mathcal{G}_{pre}''$ and replaced with the loop abstraction $\mathcal{A}$.
- Let $\mathcal{N}_{cut}$ = $nodes(\mathcal{A})$.
- We construct $\mathcal{G}_{cut}$ by including all nodes in $\mathcal{N}_{cut}$ and all edges $e$ where there exists $n, n' \in \mathcal{N}_{cut}$ where $e$ is on a path between $n$ and $n'$ in $\mathcal{G}_\textit{pre}''$.

### Step 7 - Replace Pre-State Subgraph with Abstraction Graph
The graph $\mathcal{G_h}$ for the loop head is defined as $\mathcal{G_h} = \mathcal{G}_{pre}'' \setminus \mathcal{G}_{cut} \cup \mathcal{A}$

### Step 8 (Optional) - Confirm Invariant is Correct
To confirm that the resulting graph is correct, for any back edge into the state at $\mathcal{G}_h$ with state $\mathcal{G}'$, performing the *loop join* operation on $\mathcal{G}'$ and $\mathcal{G}_h$ should yield $\mathcal{G}_h$.

[^nofail]: Such repacking should always be possible. Namely, because the nodes in $\mathcal{N}_{loop}$ must be
live at the loop head.
[^note]: If the edge is a deref expansion, only add the blocked lifetime projection
[^live]: The liveness condition could also be checked for the block after the loop (assuming there is a single block). However the result is equivalent: if any node is live at $l_h$ but not after the loop, then it must be used inside the loop, and should be part of $\mathcal{N}_{loop}$ and therefore not in $\mathcal{N}_{roots}$.
[^exist]: There should not be any suffixes of $p_b$
