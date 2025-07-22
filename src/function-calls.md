# Function Calls

Consider a function call $p_{\mathit{result}} = f(o_1, \ldots, o_n)$. Each $o_i
\in \{o_1, \ldots, o_n\}$ is an *operand* of the form  `move p | copy p | const
c`.
Let $\overline{p}$ be the set of moved operand places, and let
$\mathit{latest}(p)$ denote the program point where $p$ was last modified.

The function call abstraction is created in the `PostMain` evalution stage,
after all of the operands have been evaluated. Therefore, all places in
$\overline{p}$ are labelled, as they have been moved-out by this point.

### Creating the Function Call Abstraction Graph

The PCG constructs a *function call abstraction graph* $\mathcal{A}$ to reflect the effect of the call.

We begin by determining how $f$ may manipulate the borrows in $f$ by
constructing the bipartite graph $\mathcal{A}_0$ as follows:

<div style="padding:10px;border:1px solid #FFF">

Let $RP$ be the set of lifetime projections in $\overline{p}$. For any place $p$, we define $\tilde{p}$ as the place $p~\mathtt{at}~\mathit{latest}(p)$.

Let $S$ be the set $\{\tilde{p} \downarrow r~ \mathtt{at~PRE}~|~ p \downarrow r \in RP\}$.

Let $T$ be the set $\{\tilde{p} \downarrow r~ \mathtt{at~POST}~|~ p \downarrow r \in RP\}$.

Add all nodes in $S$ to $\mathcal{A}_0$

For each $\tilde{p}_s \downarrow r_s \in S, \tilde{p}_t \downarrow r_t \in T$
if $r_s$ is nested in $p$, and $r_t$ outlives $r_s$, we add to $\mathcal{A}_0$ a
[Function Call Abstraction Edge](./definitions/pcg-edges.html#function-call-abstraction-edge) $\{\tilde{p}_s \downarrow r_s\} \rightarrow \{\tilde{p}_t
\downarrow r_t\}$.

</div>

The function call abstraction graph $\mathcal{A}$ is constructed by adding to
$\mathcal{A}_0$ edges such that for every lifetime $r$ in $p_\mathit{result}$,
we define the set $S_r = \{\tilde{p} \downarrow r~|~\tilde{p}\downarrow
r~\text{is a leaf in}~\mathcal{G}_0 \}$, and add a `BorrowFlow` edge $S_r
\rightarrow \{p_\mathit{result} \downarrow r \}$.

### Adding the Function Call Abstraction Graph to the PCG

We add an abstraction graph $\mathcal{A}$ to a PCG $\mathcal{G}_0$ to create a new PCG $\mathcal{G}$ as follows.

First, we initialize $\mathcal{G}$ as $\mathcal{A} \cup \mathcal{G}_0$. For each projection $p \downarrow r$ in $RP$, we modify $\mathcal{G}$ as follows:
1. For each endpoint in $\mathcal{G}_0$ whose target is $p \downarrow r$, redirect the target to $\tilde{p}\downarrow r~\mathtt{at~PRE}$.
2. For each `Future` edge $p \downarrow r \rightarrow p' \downarrow r'~\mathtt{at~Future}$ in $\mathcal{G}_0$, remove the edge, and for each leaf $n$ in $\mathcal{G}_0$ with an ancestor $\tilde{p} \downarrow r~\mathtt{at PRE}, insert the `Future` edge $\{n\} \rightarrow p' \downarrow r' to $\mathcal{G}$.
3. Remove $p \downarrow r$ from $\mathcal{G}$.
