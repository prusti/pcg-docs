# Misc (To Update)

## Mutable Borrows

Consider the stmt `p = &mut q`, at a program point $l$, where $p$ has type $\&r_0 ~\mathtt{mut}~\tau$, and $q$ has type $\tau$, and $\tau$ is a type containing lifetimes $r_1, \ldots r_n$.

At the end of the `PreOperands` phase, the PCG is guaranteed to be in a state where, for each $r_i \in \{r_1, \ldots, r_n\}$ the lifetime projection $q \downarrow r_i$ is in the graph. During the `Operands` phase, each lifetime projection $q \downarrow r_i$ is *labelled* with the current program point to become $q \downarrow r_i ~\mathtt{at}~l$. At the end of the `PreMain` phase, for each $r_i \in \{r_0, \ldots, r_n\}$, the lifetime projection $p\downarrow r_i$ is guaranteed *not* to be in the graph. During the `Main` phase, these projections are added.

Subsequently, the labelled lifetime projections under $p$ are connected with `BorrowFlow` edges to the new lifetime projections under $q$. Namely, for each $i \in \{1, \ldots n\}, j \in \{0, \ldots, n\}$ if $r_i$ outlives $r_j$, then a `BorrowFlow` edge $\{q \downarrow r_i~\mathtt{at}~l\} \rightarrow \{p \downarrow r_j\}$ is added.

Subsequently, we introduce `Future` nodes and edges to account for nested references as follows. For each $i \in \{1, \ldots n\}$:

1. Insert the node $q \downarrow r_i~\mathtt{at Future}$ into the graph
2. If any `Future` edges originate from the labelled projection $q \downarrow r_i~\mathtt{at}~l$, redirect  them such that they originate from $q \downarrow r_i~\mathtt{at Future}$.
3. Insert a `Future` edge $\{q \downarrow r_i~\mathtt{at}~l\} \rightarrow \{q \downarrow r_i~\mathtt{at Future}\}$
4. Insert a `Future` edge $\{p \downarrow r_i\} \rightarrow \{q \downarrow r_i~\mathtt{at Future}\}$

## Unpacking Places

An *unpack* operation introduces an `Unpack` edge into the graph, and is associated with a *source place* $p$ and an *expansion* $\overline{p}$. An unpack operation can either be *mutable* or *read-only*.

An unpack operation is a *dereference* unpack for lifetime $r$ iff the type of the source place *p* is `&'r mut p` or `&'r p`.

Applying an unpack operation introduces an `Unpack` edge as follows:

1. If the unpack operation is a dereference operation, the edge $\{p, p \downarrow r\} \rightarrow \{*p\}$ is added to the graph.
2. Otherwise, the edge $\{p\} \rightarrow \{\overline{p}\}$ is added to the graph.

A *mutable* unpack operation for capabiliy $c \in \{W, E\}$ requires that the source place $p$ have capability $c$. When the operation is a applied, the capability for $p$ is removed and the capability of all places in $\overline{p}$ is set to $c$.

A *read-only* unpack operation requires that $p$ have capability $R$ and assigns capability $R$ to all places in $\overline{p}$.

### Updating Lifetime Projections

Assume the source place $p$ has type $\tau$ with lifetimes $r_1, \ldots, r_n$. If the unpack operation is mutable, then we label each lifetime projection $p\downarrow r_i$ with location $l$.

The *source* lifetime projection for a lifetime $r$ is $p \downarrow r~\mathtt{at}~l$ if the unpack is mutable, and $p\downarrow r$ otherwise. The *target* lifetime projections is the set $\{p' \downarrow r~|~p' \in \overline p~\text{and}~r~\text{is in the type of}~p'\}$.

For each lifetime $r \in \{r_1, \ldots, r_n\}$, if the set of target lifetime projections associated with $r$ is nonempty:

1. For each $t$ in the set of target projections, add a `BorrowFlow` edge $\{s\} \rightarrow \{t\}$ where $s$ is the source projection[^todo].

[^todo]: **TODO**: Currently we actually introduce an unpack edge in the implementation, but we should change this.

2. If the unpack is mutable and the source place of the expansion is either a reference or a borrowed place:
a. Add a `Future` edge $\{s\} \rightarrow \{p \downarrow r~\mathtt{at Future}\}$
b. For each $t$ in the set of target projections, add a `Future` edge $\{t\} \rightarrow \{p \downarrow r~\mathtt{at Future}\}$
c. If any `Future` edges originate from the source projection $s$, redirect  them such that they originate from $p \downarrow r~\mathtt{at Future}$.

## Function Calls

:::warning
Our implementation is somewhat outdated and doesn't perform this exact logic currently.
:::

Consider a function call $p_{\mathit{result}} = f(o_1, \ldots, o_n)$. Each $o_i \in \{o_1, \ldots, o_n\}$ is an *operand* of the form  `move p | copy p | const c`.
Let $\overline{p}$ be the set of moved operand places, and
let $\mathit{latest}(p)$ denote the program point where $p$ was last modified.

All places in $p$ should be labelled in the graph.

### Creating the Function Call Abstraction Graph


The PCG constructs a *function call abstraction graph* $\mathcal{A}$ to reflect the effect of the call.

We begin by determining how $f$ may manipulate the borrows in $f$ by constructing the bipartite graph $\mathcal{A}_0$ as follows:

<div style="padding:10px;border:1px solid #FFF">

Let $RP$ be the set of lifetime projections in $\overline{p}$. For any place $p$, we define $\tilde{p}$ as the place $p~\mathtt{at}~\mathit{latest}(p)$.

Let $S$ be the set $\{\tilde{p} \downarrow r~ \mathtt{at PRE}~|~ p \downarrow r \in RP\}$.

Let $T$ be the set $\{\tilde{p} \downarrow r~ \mathtt{at POST}~|~ p \downarrow r \in RP\}$.

Add all nodes in $S$ to $\mathcal{A}_0$

For each $\tilde{p}_s \downarrow r_s \in S, \tilde{p}_t \downarrow r_t \in T$  if $r_s$ is nested in $p$, and $r_t$ outlives $r_s$, we add to $\mathcal{A}_0$ a `BorrowFlowEdge` $\{\tilde{p}_s \downarrow r_s\} \rightarrow \{\tilde{p}_t \downarrow r_t\}$.

</div>

The function call abstraction graph $\mathcal{A}$ is constructed by adding to $\mathcal{A}_0$ edges such that for every lifetime $r$ in $p_\mathit{result}$, we define the set $S_r = \{\tilde{p} \downarrow r~|~\tilde{p}\downarrow r~\text{is a leaf in}~\mathcal{G}_0 \}$, and add a `BorrowFlow` edge $S_r \rightarrow \{p_\mathit{result} \downarrow r \}$.

### Adding the Function Call Abstraction Graph to the PCG

We add an abstraction graph $\mathcal{A}$ to a PCG $\mathcal{G}_0$ to create a new PCG $\mathcal{G}$ as follows.

First, we initialize $\mathcal{G}$ as $\mathcal{A} \cup \mathcal{G}_0$. For each projection $p \downarrow r$ in $RP$, we modify $\mathcal{G}$ as follows:
1. For each endpoint in $\mathcal{G}_0$ whose target is $p \downarrow r$, redirect the target to $\tilde{p}\downarrow r~\mathtt{at PRE}$.
2. For each `Future` edge $p \downarrow r \rightarrow p' \downarrow r'~\mathtt{at Future}$ in $\mathcal{G}_0$, remove the edge, and for each leaf $n$ in $\mathcal{G}_0$ with an ancestor $\tilde{p} \downarrow r~\mathtt{at PRE}, insert the `Future` edge $\{n\} \rightarrow p' \downarrow r' to $\mathcal{G}$.
3. Remove $p \downarrow r$ from $\mathcal{G}$.

## Origin Containg Loan

An origin $r$ contains a loan $r_L$ created at location $l$ iff:

**Polonius**: Read directly from output facts

**NLL**: $r_L$ is live at $l$ and $r_L$ outlives $l$
