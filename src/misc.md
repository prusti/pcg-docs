# Misc (To Update)

## Preliminary Definitions

### Definition: Type Contains

A type $\tau$ *contains* a type $\tau'$, iff:

1. $\tau = \tau'$, or
2. $\tau$ is an ADT and contains a field $\mathtt{f}: \tau_\mathtt{f}$ and $\tau_\mathtt{f}$ contains $\tau'$
3. $\tau = \mathtt{\&'r~mut}~\tau_{\text{tgt}}$ and $\tau_{\text{tgt}}$ contains $\tau'$

---

### Definition: Subplaces

A place $p'$ is a *subplace* of $p$ if $p = p'$ or the projection of $p$ is a
prefix of the projection of $p'$.

---

### Definition: Containing Lifetimes

A type $\tau$ *contains* a lifetime $r$ iff $\tau$ contains the type
$\mathtt{\&\tick{r}~mut}~\tau'$ for some type $\tau'$. A lifetime $r$ is *nested*
in a type $\tau$ iff $\tau$ contains a type $\mathtt{\&'r~mut}~\tau'$ and $\tau'$ contains $r$.
We extend these concept to places: a place $p: \tau$ contains a lifetime $r$ iff
$\tau$ contains $r$; $r$ is nested in $p: \tau$ iff $r$ is nested in $\tau$. A lifetime
projection $p \downarrow r$ is *nested* if $r$ is nested in $p$.

---

### Definition: Program Points

A program point is either `start bb | mid l | after l`, where `bb` is a MIR basic block and l is MIR location.

## Nodes

$$
\newcommand{\bb}{\mathtt{bb}}          % Basic blocks
\newcommand{\ppointbefore}[1]{{\text{before}~#1}}
\newcommand{\ppointafter}[1]{{\text{after}~#1}}
\newcommand{\ppoint}{{l}}
\newcommand{\location}{\mathtt{loc}}   % Locations
\newcommand{\placeelem}{e}    % PlaceElems
\newcommand{\rustfield}{f}
\newcommand{\rustty}{T}
\newcommand{\maybelabelled}{\tilde{p}}
\newcommand{\maybelabelledregion}{\tilde{r}}
\newcommand{\current}{\mathtt{current}}
\newcommand{\pcgplace}{\hat{p}}
\newcommand{\remote}[1]{\mathit{origin}(#1)}
\newcommand{\lifetimeproj}{\mathit{rp}}
\newcommand{\lproj}[2]{#1 \downarrow #2}
\newcommand{\const}{\mathtt{const}}
\newcommand{\lifetime}{r}
\begin{array}{l l r}
    b & ::= \bb_i & \textbf{(Basic Block)} \\
    \ppoint & ::= \ppointbefore{b}~|~\ppointafter{\location} & \textbf{(Program Point)} \\
    \placeelem & ::= .\rustfield~|~*~|~\mathtt{@}~\rustty & \textbf{(Place Element)} \\
    p & ::= & \textbf{(Rust Place)} \\
    p & ::=  \langle i, \overline{\placeelem} \rangle & \textbf{(Rust Place)} \\
    \maybelabelled & ::=  & \textbf{(Maybe-Labelled Place)} \\
    & \mid \current{}~p & \text{(Current Place)} \\
    & \mid p~\mathtt{at}~\ppoint & \text{(Labelled Place)} \\
    \maybelabelledregion & ::=  & \textbf{(Maybe-Labelled Lifetime)} \\
    & \mid \current~r & \text{(Current Lifetime)} \\
    & \mid r~\mathtt{at}~\ppoint & \text{(Labelled Lifetime)} \\
    \pcgplace & ::=  & \textbf{(PCG Place)} \\
    & \mid \maybelabelled & \text{(Maybe-Labelled Place)} \\
    & \mid \remote{i} & \text{(Remote Place)} \\
    \lifetimeproj & ::=  & \textbf{(Lifetime Projection)} \\
    & \mid \lproj{\pcgplace}{\maybelabelledregion} & \text{(Place Projection)} \\
    & \mid \lproj{\const}{\lifetime} & \text{(Constant Projection)} \\
    n & ::= \pcgplace~|~\lifetimeproj & \textbf{(PCG Node)}
\end{array}
$$

:::warning
In the implementation we currently refer to lifetime projections as "region projections" and labelled places as "old" places.
:::

## The "Latest" Map

The "Latest" map $\mathcal{L}$ is a partial map from places to program points.

The function $\mathit{latest}(p)$ is defined as follows:

$$
\mathit{latest}(p) = \begin{cases}
\mathcal{L}[p']& \text{if}~\mathcal{L}~\text{contains any subplace of}~p \\
\mathtt{start bb0}&\text{otherwise}
\end{cases}
$$

where $p'$ is the longest subplace of $p$ where $p' \in \mathcal{L}$.


## Labelling Places

To label a place $p$ in the graph, for each node in the graph, for each $\mathtt{current}~p'$ in each node, if $p'$ is a subplace of $p$ or $p$ is a subplace of $p'$, $\mathtt{current}~p'$ is replaced with the labelled place $p'~\mathtt{at}~\mathit{latest(p')}$.


## Labelling Lifetime Projections

The operation of labelling a lifetime projection $p \downarrow r$ with a program point $l$ is to replace the node in the graph with the node $p \downarrow r~\mathtt{at}~l$.

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
