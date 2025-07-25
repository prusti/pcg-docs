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

We define the "pre-call states" of $\widetilde{RP}$ as $S = \{\tilde{p}
\downarrow r~ \mathtt{at~PRE}~|~ p \downarrow r \in RP\}$.

We define the "post-call states" of $\widetilde{RP}$ as $T = \{\tilde{p}
\downarrow r~ \mathtt{at~POST}~|~ p \downarrow r \in RP~\text{and}~r~\text{is nested in}~p\}$

<div class="info">

The definitions of sets $RP$, $\widetilde{RP}$, $S$, and $T$ do *not* depend on
the nodes present in the PCG. In general, we postulate that following invariants
should always hold:

- Only the nodes in $RP$ are in the graph at the end of $\texttt{PreOperands}$ stage
- Only the nodes in $\widetilde{RP}$ are in the graph at the end of the $\texttt{PostOperands}$ stage
- Only the nodes in $S \cup T$ are in the graph at the end of the $\texttt{PostMain}$ stage

</div>

### 1. Redirect Future Nodes

This follows the standard process, e.g. similar to borrows and borrow PCG expansions

1. For each `Future` edge $e$ where the source node is in $RP$:
   1. Change the source node from $\langle \lproj{\tilde{p}}{r}\rangle$ to $\langle \tilde{p}
\downarrow r~ \mathtt{at~POST} \rangle$

### 2. Label Lifetime Projections for Pre-State

Label projections in $\widetilde{RP}$ to become $S$ in the graph:

1. For each $0 < i \leqslant |RP|$:
   1. Label the $\widetilde{RP}_i$ with $\texttt{PRE}$

### 3. Add Abstraction Edges

At a high level we construct by connecting lifetime projections $S$ to the
lifetime projections in $T$ and the lifetime projections in $p_{result}$, where
connections are made based on outlives constraints. Concretely:

1. Let $\mathcal{O}$ be union of $T$ and the lifetime projections in $p_{result}$
2. For each $\lproj{\tilde{p}}{r_s~\texttt{at~PRE}}$ in $S$:
   1. Let $\mathcal{O}_s$ contain each lifetime projection $rp \in \mathcal{O}$ where $r_s$ outlives the lifetime of $rp$
   2. If $\mathcal{O}_s$ is not empty, add the abstraction edge $\{\lproj{\tilde{p}}{r_s~\texttt{at~PRE}}\} \rightarrow \mathcal{O}_s$ to the PCG
