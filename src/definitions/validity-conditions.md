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

## Formal Definition

The representation of validity conditions in our implementations corresponds
closely to the following description:

Validity conditions $\pc \in \pcs~$ is a map $\Bb \rightarrow \powerset{\Bb}$
describing control-flow conditions. For each block $\block \in \dom{\pc}$,
$\pc[b]$ is a subset of the *real* successors of $\block$.

The *join* of validity conditions $\pc_i$ and $\pc_j$ is defined as:

$$
(\pc_i \cup \pc_j)[b] = pc_i[b] \cup pc_j[b]
$$

Validity conditions $\pc$ are *valid* for a path $b_0,~\ldots,~b_n$ iff:

$$
\forall i \in \{0, \ldots, n-1\} : \pc[b_i] = \emptyset \vee b_{i+1} \in \pc[b_i]
$$


### Correctness Theorem (Sketch)

For every borrow edge $e$ in the PCG at location $l$ and execution path
$\overline{d}$ to $l$, the corresponding borrow is live at $l$ iff
$\overline{d}$ satisfies the validity conditions of $e$.

### Proof

We prove this for each location in the MIR by induction on the basic blocks of
the graph via a reverse-postorder traversal. The inductive hypothesis is that
the property holds for each ancestor block.

Having proved for the 1st location in a basic block, it is trivial to show for
the remaining locations in the block, therefore we only concern ourselves with
the basic blocks.

The case of `bb0` is trivial.

We now concern ourselves with the validity conditions $pc^e_{n}$ of an arbitrary
edge $e$ at block $b_n$, assuming via IH that it holds for all $b_n'$ where $n'
< n$. Let $\overline{b_{in}}$ be the set of incoming nodes. We define our $pc^e_n$
as the repeated join: $\bigcup_{pc^f_e \in \overline{b_{in}}}{pc_f^e \cup \{b_f
\rightarrow b_n\}}$.

We first show that the *if* direction holds: __For every borrow edge $e$ in the
PCG at location $l$ and execution path $\overline{d}$ to $l$, if the corresponding
borrow is live at $l$, then $\overline{d}$ satisfies the validity conditions of
$e$.__


Every $\overline{d}$ has a prefix $\overline{d_f}$ and ends with $b_f
\rightarrow b_n$, by our IH we have $\overline{d_f}$ satisfies $pc_e^f$. We need
to then show that $\overline{d} = \overline{d_f} \cup b_f \rightarrow b_n $ satisfies $pc_e^n$.
Our proof is by contradiction.

Suppose $\overline{d}$ did not satisfy $pc_e^n$; then there must be a pair $(b
\rightarrow b') \in \overline{d}$  where $pc_e^n[b] \neq \emptyset \land b'
\not\in pc_e^n[b]$.  We know that the pair cannot be the final pair in
$\overline{d}$ (i.e. $b_f \rightarrow b_n$) by the definition of join we have
$pc_e^n[b_f] = \emptyset \lor b_n \in pc_e^f[b]$.  Therefore the edge $b
\rightarrow b'$ must exist in some strict prefix $\overline{d}'$ of
$\overline{d}$.  Then, there must be a nonempty set $\overline{b_f}' \subseteq \overline{b_{in}}$ where
$pc_e^{f'}[b] \neq \emptyset \land b' \not\in pc_e^{f'}[b]$ (otherwise, the
joined $pc_e^{n}[b]$ would be either $\emptyset$ or contain $b'$).  But then,
because $\overline{d}'$ must contain $b \rightarrow b'$, it would not satisfy
the validity conditions of $pc_e^{f'}$ for any $f'$ .


We now show the reverse: __For every borrow live at $l$ for an execution path
$\overline{d}$, its corresponding edge satisfies the validity conditions of $e$__.

Our proof relies on the monotonicity of joins: if $b' \in pc[b]$ then $b' \in
(pc \cup pc')[b]$ for any $pc'$.

The borrow is created at a unique block $b_c$. Then $b_c$ is
definitely in $\overline{d}$ at some index $i$ and the borrow is not killed in
any block $b_i$ for all $c < i \leqslant |\overline{d}|$.

Our proof works by building longer prefixes of $\overline{d}$. The base case is
when the borrow is created (and therefore becomes live) at $b_c = d_i$, where
the property holds trivially. Then, when going from $d_i, \ldots, d_j$ to $d_i,
\ldots, d_{j+1}$, we add to the validity conditions $d_j \rightarrow d_{j+1}$
and join other incoming blocks. Because the prefix satisfies the prior conditions by induction, satisfies the additional condition, and monotonicity of join, the longer prefix also satisfies conditions. QED.

