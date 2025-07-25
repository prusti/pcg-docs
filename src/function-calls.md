# Function Calls

Consider a function call $p_{\mathit{result}} = f(o_1, \ldots, o_n)$. Each $o_i
\in \{o_1, \ldots, o_n\}$ is an *operand* of the form  `move p | copy p | const
c`.
Let $\overline{p}$ be the set of moved operand places, and let
$\mathit{latest}(p)$ denote the program point where $p$ was last modified.

The function call abstraction is created in the `PostMain` evalution stage,
after all of the operands have been evaluated. Therefore, all places in
$\overline{p}$ are labelled, as they have been moved-out by this point.

## Algorithm

Let $RP$ be the set of lifetime projections in $\overline{p}$ (that is, obtained
from places in $p$, regardless of whether they are already in the graph). For
any place $p$, we define $\tilde{p}$ as the place
$p~\mathtt{at}~\mathit{latest}(p)$.

We define the set of lifetime projections of the moved-out operands as
$\widetilde{RP} = \{\tilde{p} \downarrow r~|~ p \downarrow r \in RP\}$.

We define the "pre-call states" of $\widetilde{RP}$ as $S = \{\tilde{p} \downarrow r~ \mathtt{at~PRE}~|~ p \downarrow r \in RP\}$.

We define  the "post-call states" of $\widetilde{RP}$ as $T = \{\tilde{p} \downarrow r~ \mathtt{at~POST}~|~ p \downarrow r \in RP\}$.

### 1. Redirect Future Nodes

This follows the standard process, e.g. similar to borrows and borrow PCG expansions

1. For each $0 < i \leqslant |RP|$:
   1. For each `Future` edge $e$ where the source node is $RP_i$
      1. Update the edge such that the source node is $T_i$

### 2. Label Lifetime Projections for Pre-State

Label projections in $\widetilde{RP}$ to become $S$ in the graph:

1. For each $0 < i \leqslant |RP|$:
   1. Label the $\widetilde{RP}_i$ with $\texttt{PRE}$

### 3. Add Abstraction Edges

At a high level we construct by :
 1. Connecting lifetime projections from $S$ to *nested* lifetime projections in $T$
 2. Connecting lifetime projections from $S$ to lifetime projections in $p_\textit{result}$

where connections are made based on outlives constraints. Concretely:

1. For each $s$ in $S$:
   1. Let $\mathcal{O} = \emptyset$ be the set of target nodes
   2. Add to $\mathcal{O}$ the each $t \in T$ where:
      1. $t$ is a nested lifetime, and
      2. The lifetime of $s$ ourlives the lifetime of $T$
   3. Add to $\mathcal{O}$ the each $rp \in p_{result}$ where the lifetime of $s$ outlives the lifetime of $rp$
   4. If $\mathcal{O}$ is not empty, add the abstraction edge $\{s\} \rightarrow \mathcal{O}$ to the PCG
