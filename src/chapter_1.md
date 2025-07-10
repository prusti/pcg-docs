# Chapter 1

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

## Liveness

A place $p$ is live at a location $l$ iff there exists a location $l'$ and a control flow-path $c$ from $l$ to $l'$ where a place *conflicting with* $p$ is used at $l'$ and there are no assignments of any places *conflicting with* $p$ along c.

## Origin Containg Loan

An origin $r$ contains a loan $r_L$ created at location $l$ iff:

**Polonius**: Read directly from output facts

**NLL**: $r_L$ is live at $l$ and $r_L$ outlives $l$

## Blocking

A lifetime projection $p\downarrow~r$ *blocks* a place $p_b$ at a location $l$ iff:

- there is a loan $p' = \mathtt{\&mut}~p_b'$ with lifetime $r_L$
- the place $p_b'$ *conflicts* with $p_b$
- $r$ contains $r_L$ at $l$


A place $p$ *blocks* a place $p_b$ at a location $l$ iff it has an associated lifetime projection $p\downarrow~r$ that blocks $p_b$.

If a node $n$ blocks a place $p_b$, then $n$ also blocks all associated lifetime projections of $p_b$.

:::info
ZG: The rules for NLL are based on the implementation in the rust_borrowck crate.

The rules for Polonius are based on the blog post description.
:::

:::info
Note that the rules for a place $p$ blocking a place $p_b$ only consider the lifetimes in the type of $p$, and do not consider its relation to the original assigned place $p'$ borrowing $p_b$. This is intentional (for example, $p$ could block $p_b$ due to the original assigned place $p'$ being moved into $p$).
:::

## Loops

The *loop head* is the basic block with an incoming back edge. We define $l_h$ as the location of the first statement of the loop head.

The *pre-loop* block is the block prior to the loop head. We assume that there is always a unique pre-loop block. The *pre-loop state* $\mathcal{G}_\textit{pre}$ is the state after evaluating the terminator of the pre-loop block.

The following operations are performed when we join the pre-loop block with the loop head. Note that at this point we've already computed $\mathcal{G}_\textit{pre}$.

We construct the state $\mathcal{G}_h$ for the loop head as follows:
At the loop head:
1. Begin by identifying $\mathcal{N}_{loop}$, the set of Borrow PCG nodes that could be modified inside the loop and later become accessible. $\mathcal{N}_{loop}$ is constructed as follows:
    - For each place $p$ *live* and *initialized* at $l_h$ that *conflicts with* any place used in the loop:
        - Add all lifetime projections of $p$ to $\mathcal{N}_{loop}$, and
        - If $p$ is not owned, add $p$ to $\mathcal{N}_{loop}$
2. The places in $\mathcal{N}_{loop}$ will need to appear in $\mathcal{G}_{h}$ but may not be present in $\mathcal{G}_{pre}$ (for example, it's possible that the loop could borrow from a subplace that requires unpacking). We construct a graph $\mathcal{G}_{pre}'$ by unpacking $\mathcal{G}_{pre}$ such that $\mathcal{G}_{pre}'$ contains all places in $\mathcal{N}_{loop}$.[^nofail]
3. We then identify $\mathcal{N}_{roots}$, the most immediate nodes that $\mathcal{N}_{loop}$ could be borrowing from and later become accessible (excluding nodes already in $\mathcal{N}_{loop})$. Note that unlike the method for deriving $\mathcal{N}_{loop}$, identifying these nodes requires considering the PCG state $\mathcal{G}_{pre}'$.
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
4. We construct an abstraction graph $\mathcal{A}$ that describes the blocking relations potentially introduced in the loop from nodes in $\mathcal{N}_\textit{roots}$ to nodes in $\mathcal{N}_{loop}$ and from nodes in $\mathcal{N}_{loop}$ to nodes in $\mathcal{N}_{loop}$.
In the process we also identify:
    - $RP_{rename}$: the lifetime projections that will need to be re-labelled in $\mathcal{G}_{h}$, and
    - $P_{blocked}$: places which will be blocked in the loop (capability will be removed in $\mathcal{G}_h$)
**Algorithm**:
    - Define the set of *blocked candidates* $\mathcal{N_\mathcal{A}} = \mathcal{N}_{roots} \cup \mathcal{N}_{loop}$
    - Define the set of *blocker candidates* $RP_B$ to contain:
        - All lifetime projections in $\mathcal{N}_{loop}$
        - For each place $p$ in $\mathcal{N}_{loop}$, the ancestor lifetime projection prior to its dereference (e.g. $p' \downarrow r$ where $*p'$ is a prefix of $p$)
    - For each non-killed borrow $b: p_a = \mathtt{\&mut}~p_b$:
      - Let $l_b$ be the location where $b$ was created
      - We begin by identifying the set of blocked nodes $\mathcal{N}_b = blocked(b)$ :
          - Let $p_b'$ be the longest prefix of $p_b$ in the related places of $\mathcal{N}_{\mathcal{A}}$[^exist], if one exists
          - If $p_b'$ exists:  $\mathcal{N}_b$ is the subset of nodes in $\mathcal{N}_\mathcal{A}$ having related place $p_b'$.
          - Otherwise: $\mathcal{N}_b = \emptyset$ (this borrow is ignored)
          - The set of candidate *blockers* $RP_b$ is the subset of $RP_B$ such that each $p \downarrow r$ in $RP_b$:
              - $p$ and $n_b$ have distinct related locals
              - $p \downarrow r$ blocks $n_b$ at $l_h$.
          - If $RP_b$ is not empty, add the related place of $n_b$ to $P_{blocked}$
          - For each $r \downarrow p \in RP_b$, insert a loop abstraction edge $\{n_b\} \rightarrow \{r \downarrow~p\}$ into $\mathcal{A}$
    -  Subsequently, ensure that $\mathcal{A}$ is well-formed by adding unpack edges where appropriate. For example, if `(*x).f` is in the graph, there should also be an expansion edge from `*x` to `(*x).f`.
    - We identify the set $RP_{rename}$ of lifetime projections that will need to be renamed (indicating they will be expanded in the loop and remain non-accessible at the loop head). $RP_{rename}$ is the set of non-leaf lifetime projection nodes in $\mathcal{A}$ (leaf nodes are accessible at the head).
    - Label all lifetime projections in $RP_{rename}$ with location $l_h$, add connections to their `Future` nodes as necessary.
6. The resulting graph for the loop head will require new labels on lifetime projections modified in the loop. We begin by constructing an intermediate  graph $\mathcal{G}_{pre}''$  by labelling each lifetime projection in $RP_{rename}$ with $l_h$ and remove capabilities to all places in $P_{remove}$ in $\mathcal{G}_{pre}'$.
 6. We then identify the subgraph $\mathcal{G}_{cut} \subseteq \mathcal{G}_{pre}''$ that will be removed from $\mathcal{G}_{pre}''$ and replaced with the loop abstraction $\mathcal{A}$.
    - Let $\mathcal{N}_{cut}$ = $nodes(\mathcal{A})$.
    - We construct $\mathcal{G}_{cut}$ by including all nodes in $\mathcal{N}_{cut}$ and all edges $e$ where there exists $n, n' \in \mathcal{N}_{cut}$ where $e$ is on a path between $n$ and $n'$ in $\mathcal{G}_\textit{pre}''$.

7.  The graph $\mathcal{G_h}$ for the loop head is defined as $\mathcal{G_h} = \mathcal{G}_{pre}'' \setminus \mathcal{G}_{cut} \cup \mathcal{A}$

8. To confirm that the resulting graph is correct, for any back edge into the state at $\mathcal{G}_h$ with state $\mathcal{G}'$, performing the *loop join* operation on $\mathcal{G}'$ and $\mathcal{G}_h$ should yield $\mathcal{G}_h$.

[^nofail]: Such repacking should always be possible. Namely, because the nodes in $\mathcal{N}_{loop}$ must be
live at the loop head.
[^note]: If the edge is a deref expansion, only add the blocked lifetime projection
[^live]: The liveness condition could also be checked for the block after the loop (assuming there is a single block). However the result is equivalent: if any node is live at $l_h$ but not after the loop, then it must be used inside the loop, and should be part of $\mathcal{N}_{loop}$ and therefore not in $\mathcal{N}_{roots}$.
[^exist]: There should not be any suffixes of $p_b$
