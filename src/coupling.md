# Coupling (WIP)

The PCG tracks ownership and borrowing at a fine-grained level, and in some
cases this granularity cannot be "observed" by the type system. For example,
lifetime projection nodes can represent a notion of reborrowing that is more
precise than Rust's borrow-checker itself. For example, consider the `choose`
function:

```rust
fn choose<'a, T>(choice: bool, lhs: &'a mut T, rhs: &'a mut T) -> &'a mut T {
    if choice {
        lhs
    } else {
        rhs
    }
}
```

The the PCG shape of a call `choose(x, y)` function: consists of two edges
$\lprojtt{x}{\tick{a}} \rightarrow \lprojtt{result}{\tick{a}}$ and
$\lprojtt{y}{\tick{a}} \rightarrow \lprojtt{result}{\tick{a}}$. However, because
the compiler only tracks lifetimes, the borrows of `x` and `y` will always
expire at the same time. Accordingly, the two edges corresponding to the call
will always be removed from the graph at the same time. These edges are
therefore _coupled_, because the Rust type system forces the PCG to remove them
at the same time.

## Motivation

Because the type systems forces a set of coupled edges to be removed
"all-at-once", edges that are known to be coupled could be treated as
a single hyperedge.

The primary reason for doing so is to provide more information analysis tools.
For example, Prusti uses coupling information to generate the shape of magic
wands: in the `choose`, the coupled hyperedge provides precisely the shape of
magic wand that Prusti encodes (although this is not always the case).

Another benefit is that coupling can reduce the size of the graphs.

## Formal Definitions

### Hyperedge

A hyperedge $e$ is an object with an associated set of _source nodes_ and
_target nodes_. The functions $\sources(e)$ and $\targets(e)$ denote the source
and target nodes respectively.

### Coupled Edges

A _coupled edge_ $c$ is a hyperedge defined by a set of _underlying_ hyperedges,
where the sources and targets are defined as follows:

Let $S$ be the union of the sources of $\overline{e}$ and $T$ be the union of
the targets of $T$. Then $sources(c) = S \setminus T$ and $targets(c) = T
\setminus S$.

### Hypergraph

A hypergraph $G$ is a tuple $\langle S, E \rangle$ where $S$ is a set of nodes and $E$ is a set
of hyperedges. Functions $nodes(G)$ and $edges(G)$ return the sets of nodes and
hyperedges respectively.

### Blocked Nodes

A node $n$ is _blocked_ in $G$ iff $n \in nodes(G)$ and $n$ is not a leaf in $G$.

### Descendant Relation

We define the _descendant_ relation $\descendant$ as

$$
  s~\descendant~s'~\text{iff}~s = s'~\text{or}~s~\text{is a descendant of}~s'~\text{in}~G.
$$

### Frontier

A set of nodes $S$ is a _frontier_ of a hypergraph $G$ (denoted $\frontier(S,
G)$) iff $S \subseteq nodes(G)$ and $S$ is closed under $\descendant$.

If $S$ is a frontier of $G$, it defines a _valid expiry_. The _valid expiry_
$\validexpiry{S}{G}$ is the subgraph of $G$ obtained by removing all
nodes in $S$ and all edges containing sources or targets in $S$. The _expired edges_ of a valid

### Reachable Subgraph

A graph $G'$ is a *reachable subgraph* of a graph $G$ iff there exists a
frontier $S$ such that $\validexpiry{S}{G} = G'$

## Desired Properties of Coupled Edges

Edges that will always be removed from the graph at the same time should
definitely be coupled. Formally:

A set of edges $\overline{e}$ _expire together_ on a graph $G$ iff for all
reachable subgraphs $G'$, $G'$ either contains all edges in $\overline{e}$ or
none of them, i.e.:
1. $\overline{e} \cap edges(G) = \overline{e}$, or
2. $\overline{e} \cap edges(G) = \emptyset$

If a set of edges $\overline{e}$ expire together on a graph $G$, then there must
exist a set of edges $\overline{e'} \supseteq \overline{e}$ that are coupled for
$G$.

<!-- ### Candidate Definitions

At a high level, there are two possible definitions of coupling we could consider:

1. A set of edges $E$ is coupled iff it is an equivalence class induced by $\sim$
2. A set of edges $E$ is coupled iff, for some nonempty set of nodes $N$ that the compiler
   requires to be unblocked simultanesouly, it is the smallest set of edges that unblocks
   all nodes in $N$ and is the union of equivalence classes induced by $\sim$.

Def. (1) defines coupling solely in terms of what Rust's type system is capable
of tracking, while (2) is based on possible states that could possibly be
_observed_ in terms of places.

To demonstrate the difference, lets consider the `m` function:

```rust
fn m<'a: 'c, 'b: 'e, 'c, 'd, 'e, T>(
    x: &'a mut T,
    y: &'b mut T,
) -> (&'c mut T, &'d mut T, &'e mut T)
    where 'a: 'd, 'b: 'd {
         unimplemented!()
}
```

In `m`, argument `x` is blocked by lifetimes `'c` and `'d`, and `y` is blocked
by `'d` and `'e`. The shape of the function therefore looks like:

```hypergraph
{
  "height": "300px",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 300, "y": 100},
    {"id": "result_c", "place": "result", "lifetime": "'c", "x": 0, "y": 200},
    {"id": "result_d", "place": "result", "lifetime": "'d", "x": 200, "y": 200},
    {"id": "result_e", "place": "result", "lifetime": "'e", "x": 400, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_c"]},
    {"sources": ["x_a"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_e"]}
  ]
}
```

From the caller's perspective, the expiry of `'d` is tracked by the type system
but is not sufficient on its own to unblock either `x` and `y`.

Under definition (1) the expiry of `'d` is relevant, with the resulting coupled graph appearing as:

```hypergraph
{
  "height": "300px",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 300, "y": 100},
    {"id": "result_c", "place": "result", "lifetime": "'c", "x": 0, "y": 200},
    {"id": "result_d", "place": "result", "lifetime": "'d", "x": 200, "y": 200},
    {"id": "result_e", "place": "result", "lifetime": "'e", "x": 400, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_c"]},
    {"sources": ["x_a"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_e"]},
    {"sources": ["x_a"], "targets": ["result_c"], "style": "coupled"},
    {"sources": ["y_b"], "targets": ["result_e"], "style": "coupled"},
    {"sources": ["x_a", "y_b"], "targets": ["result_d"]}
  ]
}
```

Under definition (2), coupled edges must include an unblocked node. Because $\lprojtt{x}{a}$ and $\lprojtt{y}{b}$ can expire independently, the resulting graph has two (partially overlapping) coupled edges:

```hypergraph
{
  "height": "300px",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 300, "y": 100},
    {"id": "result_c", "place": "result", "lifetime": "'c", "x": 0, "y": 200},
    {"id": "result_d", "place": "result", "lifetime": "'d", "x": 200, "y": 200},
    {"id": "result_e", "place": "result", "lifetime": "'e", "x": 400, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_c"]},
    {"sources": ["x_a"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_e"]},
    {"sources": ["x_a", "y_b"], "targets": ["result_c", "result_d"]},
    {"sources": ["x_a", "y_b"], "targets": ["result_d", "result_e"]}
  ]
}
``` -->

Note that we could in principle define coupling as such, but we could also
consider a stronger definition we describe below:

## Definition Based on Unblocking Frontier Expiries

Our stronger definition is based on the following two observations:

First, if removing a frontier $S$ does not unblock any node in a graph, there is
no way for the removal to be observed in the program. Therefore, such frontiers
do not need to be considered for the purpose of asserting properties about a
place once it becomes accessible. We can instead define coupling via notion of
*unblockings* of a graph, where an unblocking is an ordered list of the sets of
nodes that become available by repeated removal of frontiers.

### Unblockings

An _unblocking_ $U$ of a graph $G$ is an ordered partitioning of the non-root
nodes of $G$ into non-empty subsets $S_1, \ldots, S_n$, satisfying the property
that there exists a frontier $S'$ of $G$ with an expiry that unblocks all nodes
in $S_1$, and $S_2, \ldots S_n$ is an unblocking of $G \setminus S'$.  The
function $\unblockings(G)$ denotes the set of all unblockings of $G$.


Correspondingly, we can define edges as coupled if they always *observably*
expire together, i.e. at all points when a node becomes accessible, they are
either all in the graph or none of them are.

### Reachable Subgraphs

Formally, for a graph $G_0$ and an unblocking $U = S_1, \ldots, S_n$ of $G_0$,
the _reachable subgraphs_ $\reachable(U, G_0)$ of an unblocking $U = S_1,
\ldots, S_n$ is the list of graphs $G_0, \ldots, G_n$ where $\forall i, 1
\leqslant i \leqslant n~.~G_{i} = G_{i-1} \setminus S_{i}$.
The function $\reachableset$ is the lifting of $\reachable$ to sets of unblockings:
$$\reachableset(\overline{U}, G) = \bigcup_{U \in \overline{U}} \reachable(U, G)$$

Therefore, edges should be coupled if they are either all present or all absent
for each graph in $\reachableset(\unblockings(G), G)$.

The second observation is that this set can be computed by considering only a
subset of the unblockings in $G$.  This is because an unblocking $U$ can
*subsume* an unblocking $U'$ in the sense that the reachable subgraphs of $U$
are a superset of the reachable subgraphs of $U'$.

### Subsumption

An unblocking $U = S_1, \ldots, S_n$ is _immediately subsumed by_ an unblocking
$U' = S'_1, \ldots S'_{n+1}$ (denoted $Sub(U, U')$) iff there exists an $i, 0
\leqslant i \leqslant n$ such that $S_i = S'_i \cup S'_{i+1}$ and $\forall j <
i~.~S_j = S'_j$ and $\forall j > i + 1 . S_j = S'_{j+1}$.

$U'$ *subsumes* $U$ (denoted $U < U'$) iff $\langle U, U' \rangle$ is in the
transitive closure of $Sub$.

__Theorem (Subsumption)__: If $U < U'$, then $\reachable(G, U) \subset \reachable(G, U')$

### Distinct Unblockings

The _distinct unblockings_ of a graph $G$ (denoted $\dunblockings(G)$) is the
subset of $G's$ unblockings obtained by removing all non-minimal elements w.r.t
$<$.

__Theorem (Distinct Unblockings)__: For all graphs $G$,
$\reachableset(\unblockings(G), G) = \reachableset(\dunblockings(G), G)$

### Effective and Maximal Coupling

A set of edges $\overline{e}$ are _effectively coupled_ for a graph $G_0$ iff
for all reachable subgraphs $G'$ in the distinct unblockings of $G$, $G'$
contains either all edges in $\overline{e}$ or none of them. A set of edges
$\overline{e}$ is _maximally coupled_ if it is effectively coupled and not a
subset of an effectively coupled set.

#### Theorem (Correctness)

If a set of edges $\overline{e}$ expire together on a graph $G$, then there
exists a set of edges $\overline{e'} \supseteq \overline{e}$ that are _maximally
coupled_ on $G$.

### Proof

Recall that a set of edges $\overline{e}$ expire together on $G$ if every
reachable subgraph $G'$ either contains all edges in $\overline{e}$ or none of
them, and that a set of edges are definitely coupled if for all reachable
subgraph $G''$ in the distinct unblockings of $G$ contains either all edges in
$\overline{e}$ or none of them.

Therefore it is sufficient to show that the reachable subgraphs in the distinct
unblockings of $G$ is a subset of the reachable subgraphs of $G$. The proof
makes use of the following lemma:

#### Lemma: Valid Expiry on Unions of Frontier Nodes

If $S$ is a frontier of $G$ and $S'$ is a frontier of $\validexpiry{S}{G}$, then
$S \cup S'$ is a frontier of $G$ and:

$$\validexpiry{S'}{\validexpiry{S}{G}} = \validexpiry{(S \cup S')}{G}$$

Proof is TODO

Then, let $U$ be an arbitrary unblocking of $G$, it follows by induction on the
list of frontiers corresponding to the nodes in $U$, that any for every
reachable subgraph $G'$ of $U$, there exists a frontier $S$ of $G$ such that
$\validexpiry{S}{G} = G'$.  Therefore, for all unblockings $U$ of $G$, the
reachable subgraphs of $U$ are a subset of the reachable subgraphs of $G$.

<!-- #### Lemma: Frontier Decomposition

If $S$ is a set of at least two nodes and $S$ is a frontier of $G$, then there
exists sets $S', S''$ such that $S = S' \cup S''$, $S'$ is a frontier of $G$,
and $S''$ is a frontier of $\validexpiry{S'}{G}$.

Proof is TODO -->


<!-- ## Definition Based on Productive Expiries

We define the set of coupled edges by providing an algorithm that generates
them based on a notion of _minimal productive expiry_, which we define as follows:

We say that the expiry of a frontier $S$ makes a node $n$ _accessible_ iff $n$
is blocked in $G$ and is a leaf in $G \setminus S$. An expiry of a frontier $S$
is _productive_ if it makes at least one node accessible. The _expiry edge_ of a
productive expiry is a coupled hyperedge constructed from the edges present in
$G$ and absent in $G \setminus S$.

A frontier $S$ defines a _minimal productive expiry_ of a hypergraph $G$ iff
its expiry is productive and there does not exist any $S' \subset S$ such that
$S'$ defines a productive expiry on $G$.

Then, we define the set of coupled edges for a graph $G$ via the function
$couple: G \rightarrow \powerset{E}$, which is implemented as follows:

1. Let $C = \emptyset{}$ be the set of coupled edges.
2. While $G$ contains any hyperedges:
   1. For each frontier $S$ that defines a minimal productive expiry of $G$:
      1. Add the expiry edge of $S$ to $C$
      2. $C \leftarrow C \cup couple(G \setminus S)$
3. Return $C$

### Properties

The
_unblocking expiry edges_ of an unblocking of $G$ is an ordered list $e_1,
\ldots, e_n$ corresponding to the expiry edges of the corresponding frontiers.

Then can then prove that for every unblocking $U$ of $G$, the following property holds:

For every unblocking expiry edge $e$ in $U$, either $e \in coupled(G)$, or $e$
has a set of underlying edges $E$ and $E \subseteq coupled(G)$

#### Proof

Our proof requires the following lemma:

The valid

Our proof goes by induction on the list $U$. The property holds trivially for
the base case where $U$ is empty.

We then need to show that expiry edge $e_1$ that unblocks $U_1$ is either in
$coupled(G)$ or is a combination of edges in $coupled(G)$. -->

<!-- ## Merged Unblocking Frontier Expiries

The _merged unblocking frontier expiries_ algorithm takes the coupled edges
computed by the unblocking frontier expiries algorithm and performs an additional
merging step to ensure that removing any coupled edge unblocks at least one node.

### Motivation

The unblocking frontier expiries algorithm produces maximally coupled edges, but
these edges don't necessarily satisfy the property that removing each individual
coupled edge unblocks a node. For example, in the `m` function graph, the
algorithm may produce coupled edges where some don't directly unblock a source node.

The merged algorithm addresses this by grouping coupled edges based on which
nodes they unblock, ensuring that each resulting coupled edge corresponds to the
expiry that unblocks a specific node.

### Algorithm

Given a graph $G$ and the coupled edges $C$ from the unblocking frontier
expiries algorithm:

1. For each node $n \in nodes(G)$:
   1. Let $E_n = \\{c \in C \mid n \in sources(c)\\}$ be the set of coupled edges whose sources contain $n$
   2. If $E_n \neq \emptyset$, create a new coupled hyperedge $c_n$ whose underlying edges are $\bigcup_{c \in E_n} underlyingEdges(c)$
2. Let $M$ be the set of all $c_n$ (removing duplicates)
3. Filter out redundant edges: Remove any edge $E \in M$ if there exist distinct edges $E_1, E_2 \in M$ such that $underlyingEdges(E_1) \cup underlyingEdges(E_2) = underlyingEdges(E)$
4. Return the filtered set

**Rationale for filtering**: If a coupled edge $E$ can be expressed as the union
of two other coupled edges $E_1$ and $E_2$, then unblocking $E$ is equivalent to
unblocking $E_1$ and $E_2$ in sequence. Therefore, $E$ is redundant and can be
safely removed without losing any information about the unblocking structure of
the graph.

### Properties

**Overlapping Coupled Edges**: Unlike the unblocking frontier expiries algorithm,
the merged algorithm produces coupled edges that may overlap. That is, two
different coupled edges may share some underlying edges. This is necessary to
ensure that each coupled edge corresponds to unblocking a specific node.

**Unblocking Invariant**: For every coupled edge $c$ in the result, removing $c$
from $G$ unblocks at least one node whose place corresponds to a source of $c$.

### Example: The `m` Function

For the `m` function graph (shown below in Test Graphs), the merged algorithm
produces two overlapping coupled edges:

1. $\\{x_a, y_b\\} \rightarrow \\{result_c, result_d\\}$ — Removing this unblocks $x$
2. $\\{x_a, y_b\\} \rightarrow \\{result_d, result_e\\}$ — Removing this unblocks $y$

Note that both coupled edges share the underlying edge from $x_a$ to $result_d$
and from $y_b$ to $result_d$, demonstrating the overlap property. -->

## Test Graphs

### `m` function

```rust
fn m<'a: 'c, 'b: 'e, 'c, 'd, 'e, T>(
    x: &'a mut T,
    y: &'b mut T,
) -> (&'c mut T, &'d mut T, &'e mut T)
    where 'a: 'd, 'b: 'd {
         unimplemented!()
}
```

```hypergraph
{
  "height": "300px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 300, "y": 100},
    {"id": "result_c", "place": "result", "lifetime": "'c", "x": 0, "y": 200},
    {"id": "result_d", "place": "result", "lifetime": "'d", "x": 200, "y": 200},
    {"id": "result_e", "place": "result", "lifetime": "'e", "x": 400, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_c"]},
    {"sources": ["x_a"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_e"]}
  ]
}
```

### `w` function

```rust
fn w<'a: 'd, 'b: 'd, 'c: 'e, 'd, 'e T>(
    x: &'a mut T,
    y: &'b mut T,
    z: &'c mut T,
) -> (&'d mut T, &'e mut T) where 'b: 'e {
         unimplemented!()
}
```

```hypergraph
{
  "height": "300px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 50, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 200, "y": 100},
    {"id": "z_c", "place": "z", "lifetime": "'c", "x": 350, "y": 100},
    {"id": "result_d", "place": "result", "lifetime": "'d", "x": 120, "y": 200},
    {"id": "result_e", "place": "result", "lifetime": "'e", "x": 280, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_d"]},
    {"sources": ["y_b"], "targets": ["result_e"]},
    {"sources": ["z_c"], "targets": ["result_e"]}
  ]
}
```

### Previous Example

```hypergraph
{
  "height": "300px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "a", "place": "a", "x": 0, "y": 0},
    {"id": "b", "place": "b", "x": 100, "y": 0},
    {"id": "c", "place": "c", "x": -80, "y": 100},
    {"id": "d", "place": "d", "x": 60, "y": 100},
    {"id": "e", "place": "e", "x": 150, "y": 100}
  ],
  "edges": [
    {"sources": ["a"], "targets": ["c"], "label": "1"},
    {"sources": ["b"], "targets": ["c"], "label": "2"},
    {"sources": ["a"], "targets": ["d"], "label": "3"},
    {"sources": ["b"], "targets": ["d"], "label": "4"},
    {"sources": ["b"], "targets": ["e"], "label": "5"}
  ]
}
```

## Additional Examples from HackMD

### One Lifetime Reborrower Function

```rust
fn f<'a>(x: &'a mut T) -> &'a mut T {
    x
}
```

```hypergraph
{
  "height": "250px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "result_a", "place": "result", "lifetime": "'a", "x": 100, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_a"]}
  ]
}
```

### Possible Outlives Reborrower Function

```rust
fn f<'a, 'b: 'a>(x: &'a mut T, y: &'b mut T) -> &'a mut T {
    todo!()
}
```

```hypergraph
{
  "height": "300px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "x_a", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "y_b", "place": "y", "lifetime": "'b", "x": 300, "y": 100},
    {"id": "result_a", "place": "result", "lifetime": "'a", "x": 200, "y": 200}
  ],
  "edges": [
    {"sources": ["x_a"], "targets": ["result_a"]},
    {"sources": ["y_b"], "targets": ["result_a"]}
  ]
}
```

### Non-Bipartite Graph Example

```hypergraph
{
  "height": "350px",
  "couplingAlgorithms": "all",
  "nodes": [
    {"id": "x1", "place": "x1", "x": 50, "y": 50},
    {"id": "y1", "place": "y1", "x": 50, "y": 200},
    {"id": "a", "place": "a", "x": 250, "y": 70},
    {"id": "c", "place": "c", "x": 180, "y": 150},
    {"id": "b", "place": "b", "x": 280, "y": 220},
    {"id": "x", "place": "x", "x": 400, "y": 80},
    {"id": "y", "place": "y", "x": 420, "y": 220}
  ],
  "edges": [
    {"sources": ["x1"], "targets": ["a"]},
    {"sources": ["a"], "targets": ["b"]},
    {"sources": ["b"], "targets": ["x"]},
    {"sources": ["y1"], "targets": ["c"]},
    {"sources": ["c"], "targets": ["y"]},
    {"sources": ["x1"], "targets": ["c"]},
    {"sources": ["c"], "targets": ["a"]},
    {"sources": ["a"], "targets": ["x"]},
    {"sources": ["y1"], "targets": ["b"]},
    {"sources": ["b"], "targets": ["y"]}
  ]
}
```

<!-- ## Defining Coupling Based on an _Expires After_ Relation

<div class="warning">
This isn't currently workable right now but
</div>

### Preliminaries

A hyperedge $e$ is an object with an associated set of _source nodes_ and
_target nodes_. The functions $\sources(e)$ and $\targets(e)$ denote the source
and target nodes respectively.

A _coupled edge_ $c$ is a hyperedge defined by a set of _underlying_ hyperedges,
where the sources and targets are defined as follows:

Let $S$ be the union of the sources of $\overline{e}$ and $T$ be the union of
the targets of $T$. Then $sources(c) = S \setminus T$ and $targets(c) = T
\setminus S$.

A hypergraph $G$ is a tuple $\langle S, E \rangle$ where $S$ is a set of nodes and $E$ is a set
of hyperedges. Functions $nodes(G)$ and $edges(G)$ return the sets of nodes and
hyperedges respectively.

A node $n$ is _blocked_ in $G$ iff $n \in nodes(G)$ and $n$ is not a leaf in $G$.

We define the _descendant_ relation $\descendant$ as

$$
  s~\descendant~s'~\text{iff}~s = s'~\text{or}~s'\text{is a descendant of}~s~\text{in}~G.
$$

A set of nodes $S$ is a _frontier_ of a hypergraph $G$ (denoted $\frontier(S,
G)$) iff $S \subseteq nodes(G)$ and $S$ is closed under $\descendant$.

If $S$ is a frontier of $G$, it defines a _valid expiry_. The _valid expiry_
$\validexpiry{S}{G}$ is the subgraph of $G$ obtained by removing all
nodes in $S$ and all edges containing sources or targets in $S$. The _expired edges_ of a valid

We define coupling in terms of the _expires after_ relation $\expiresafter$,
where $e_1~\expiresafter~e_2$ iff:

$$
\forall~S \subseteq nodes(G),~ n \in sources(e_1).~\\
  \frontier(S, G) \land \neg blocked(n, \validexpiry{S}{G}) \implies
  e_2 \not\in edges(\validexpiry{S}{G})
$$

Intuitively, this definition captures the notion that $e_1$ expires before $e_2$
in any expiry of the graph that unblocks a source node of $e_1$ also removes
$e_2$.

We note, however, that $\expiresafter$ is not actually transitive.

```hypergraph
{
  "height": "300px",
  "nodes": [
    {"id": "a", "place": "a", "x": 0, "y": 0},
    {"id": "b", "place": "b", "x": 100, "y": 0},
    {"id": "c", "place": "c", "x": -80, "y": 100},
    {"id": "d", "place": "d", "x": 60, "y": 100},
    {"id": "e", "place": "e", "x": 150, "y": 100}
  ],
  "edges": [
    {"sources": ["a"], "targets": ["c"], "label": "1"},
    {"sources": ["b"], "targets": ["c"], "label": "2"},
    {"sources": ["a"], "targets": ["d"], "label": "3"},
    {"sources": ["b"], "targets": ["d"], "label": "4"},
    {"sources": ["b"], "targets": ["e"], "label": "5"}
  ]
}
```

In the above graph we have $e_1~\expiresafter~e_4$ and $e_4 ~\expiresafter~e_5$ but $e_1 \not\geqslant_G e_5$.

$e_1~\expiresafter~e_4$ holds because the only expiry that unblocks $a$ also removes $d$ and therefore removes $e_4$.

$e_4~\expiresafter~e_5$ holds because any expiry that unblocks $b$ must remove $e_5$.

$e_1~\expiresafter~e_5$ does _not_ hold because the expiry that unblocks $a$ only retains $e_5$.

### Definition Based on $\expiresafter$

We say that edges $e_1$ and $e_2$ _expire together_ iff the relation $e_1 \approx_G e_2$ holds. We define $\approx_G$ as:

$$
e_1 \approx_G e_2~\text{iff}~e_1\expiresafter~e_2~\text{and}~e_2\expiresafter~e_1
$$

We note that $\approx_G$ does **not** define an equivalence relation because the
underlying relation $\expiresafter$ is not transitive. Extending $\expiresafter$
to include its transitive closure would trivially ensure transitivity but would
not work for our notion of coupling: it would couple all edges in the above
graph (which is undesirable because $a$ can be unblocked before $b$). -->
