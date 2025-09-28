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
therefore *coupled*, because the Rust type system forces the PCG to remove them
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

## Formally Defining Coupling

A pair of edges $e_1$ and $e_2$ are *definitely coupled* (denoted $e_1 \approx
e_2$) if the type system ensures they will always be removed at the same time.
Note that $\approx$ is an equivalence relation.

We describe *coupling* as a predicate on *sets* of edges.

At a high level, there are two possible definitions of coupling we could consider:

1. A set of edges $E$ is coupled iff it is an equivalence class induced by $\approx$
2. A set of edges $E$ is coupled iff, for some nonempty set of nodes $N$ that the compiler
   requires to be unblocked simultanesouly, it is the smallest set of edges that unblocks
   all nodes in $N$ and is closed under $\approx$.

Def. (1) defines coupling solely in terms of what Rust's type system is capable
of tracking, while (2) is based on possible states that could possibly be
*observed* in terms of places.

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

Under definition (1)  the expiry of `'d` is relevant, with the resulting coupled graph appearing as:

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


<!-- For example, consider the function:

```rust
fn f<'a: 'b, 'b, T>(x: &'a mut T, y: &'a mut T, z: &'b mut T) -> (&'a mut T, &'b mut T) {
    unimplemented!()
}

For example consider the `w` function:

```rust
fn w<'a: 'd, 'b: 'd, 'c: 'e, 'd, 'e, T>(
    x: &'a mut T,
    y: &'b mut T,
    z: &'c mut T,
) -> (&'d mut T, &'e mut T)
    where 'b: 'e {
         unimplemented!()
}
```

-->
