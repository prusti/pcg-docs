# Validity Conditions

We associate borrow PCG edges with *validity conditions* to identify the
control-flow conditions under which they are valid. Consider the following
program:

```rust
fn main(){
    // BB0
    let mut x = 1;
    let mut y = 2;
    let mut z = 3;
    let mut r = &mut x;
    if rand() {
        // BB1
        r = &mut y;
    }
    // BB2
    if rand2() {
        // BB3
        r = &mut z;
    }
    // BB4
    *r = 5;
}
```

We represent control flow using a primitive called a *branch choice* $d \in D$
of the form $b_i \rightarrow b_j$. A branch choice represents the flow of
control from one basic block to another. In the above code there are two
possible branch choices from `bb0`: $\texttt{bb0} \rightarrow \texttt{bb1}$ and
$\texttt{bb0} \rightarrow \texttt{bb2}$ and one branch choice from `bb1` (to
`bb2`).

For any given basic block $b$ in the program, an *execution path* leading to $b$
is an ordered list $\overline{d} \in \powerset{D}$ of branch choices. For
example, one path of execution to `bb4` can be described by: $\texttt{bb0}
\rightarrow \texttt{bb2} \rightarrow \texttt{bb3} \rightarrow \texttt{bb4}$.

Validity conditions $\pc$ conceptually define a predicate on *execution paths*.
For example, the validity conditions $\pc_{x \rightarrow r}$ describing the
control flow where `r` borrows from `z` at `bb3` require that the path contain
$\texttt{bb2} \rightarrow \texttt{bb3}$.

We represent validity conditions $\pc$ as a partial function $B \rightarrow
  \powerset{B}$ mapping *relevant blocks* to sets of *allowed target blocks*.

An execution path $\overline{d}$ is valid for validity conditions $\pc$ iff, for
each $b_s \rightarrow b_t \in \overline{d}$, either:

- $b_s$ is not a relevant block in $\pc$, or
- $b_t$ is in the set of allowed target blocks of $b_s$ in $\pc$

<div class="warning">

TODO: Explain how validity conditions are initially determined when creating a
new edge at a basic block (inherent VCs). Describe the join informally.

</div>

## Formal Definition

Validity conditions $\pc \in \pcs~$ is a map $\Bb \rightarrow \powerset{\Bb}$
describing control-flow conditions. For each block $\block \in \dom{\pc}$,
$\pc[b]$ is a strict subset of the *real* successors of $\block$.

The *join* of validity conditions $\pc_i$ and $\pc_j$ is defined as:


$$
(\pc_i \cup \pc_j)[b] =
\begin{cases}
  \emptyset & \text{if } \pc_i[b] \cup \pc_j[b] = \text{succ}_{\mathit{real}}(b) \\
  \pc_i[b] \cup \pc_j[b] & \text{otherwise}
\end{cases}
$$

Validity conditions $\pc$ are *valid* for a path $b_0,~\ldots,~b_n$ iff:

$$
\forall i \in \{0, \ldots, n-1\} : \pc[b_i] = \emptyset \vee b_{i+1} \in \pc[b_i]
$$

<div class="info">

The intuition behind the first case of the join is that if whether a borrow is
live does not depend on what successor is taken from some basic block $b$, then
it is not necessary to store a predicate about $b$.

This is kind of an optimization, actually removing this case for the join would
not have any difference on whether the resulting validity conditions are valid
for any block. In the implementation this is useful so we can have a canonical
representation (and also reduces the size of the data structure).

</div>


