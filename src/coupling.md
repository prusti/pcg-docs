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

## Some Candidate Definitions of Coupling

### Preliminaries

A pair of edges $e_1$ and $e_2$ are _definitely coupled_ (denoted $e_1 \sim
e_2$) if the type system ensures they will always be removed at the same time.
Note that $\sim$ is an equivalence relation. We describe _coupling_ as a
predicate on _sets_ of edges.

### Candidate Definitions

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
```

## Defining Coupling Based on an _Expires After_ Relation

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
graph (which is undesirable because $a$ can be unblocked before $b$).

## Definition Based on Frontier Expiries

An _unblocking_ $U$ of a graph $G$ is an ordered partitioning of the non-root
nodes of $G$ into non-empty subsets $S_1, \ldots, S_n$, satisfying the property
that there exists a frontier $S'$ of $G$ with an expiry that unblocks all nodes
in $S_1$, and $S_2, \ldots S_n$ is an unblocking of $G \setminus S'$. For a
graph $G_0$ and an unblocking $U = S_1, \ldots, S_n$ of $G_0$, the
_reachable subgraphs_ of an unblocking $U = S_1, \ldots, S_n$ is the list of
graphs $G_0, \ldots, G_n$ where $\forall i, 1 \leqslant i \leqslant n~.~G_{i} =
G_{i-1} \setminus S_{i}$. The _transition graphs_ of $U$ is the set of pairs of
reachable subgraphs given by $\{\langle G_i, G_i+1 \rangle~|~0 \leqslant i <
n\}$.

An unblocking $U = S_1, \ldots, S_n$ is _immediately subsumed by_ an unblocking
$U' = S'_1, \ldots S'_{n+1}$ iff there exists an $i, 0 \leqslant i \leqslant n$
such that $S_i = S'_i \cup S'_{i+1}$ and $\forall j < i~.~S_j = S'_j$ and
$\forall j > i + 1 . S_j = S'_{j+1}$. We have $U < U'$ iff $U'$ is transitively
subsumed by $U$.

The _distinct unblockings_ of a graph $G$ is the subset of $G's$ unblockings
obtained by removing all non-minimal elements w.r.t $<$.

A set of edges $E$ are _effectively coupled_ for a graph $G_0$ iff for all
reachable subgraphs $G'$ in the distinct unblockings of $G$, $G'$ contains
either all edges in $E$ or none of them. A set of edges $E$ is _maximally
coupled_ if it is effectively coupled and not a subset of an effectively coupled
set.

## Definition Based on Productive Expiries

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
$coupled(G)$ or is a combination of edges in $coupled(G)$.

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
  "couplingAlgorithms": ["frontier-expiries"],
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
  "couplingAlgorithms": ["frontier-expiries"],
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
  "couplingAlgorithms": ["frontier-expiries"],
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
