# Function Shapes

## Background

The PCG generates a "shape" for a function call - a bipartite graph indicating
where borrows could flow as a result of the call. In particular this shape
represents (1) reborrows that are returned from the function (w.r.t borrows
passed in the arguments), and (2) the effects of the nested borrows passed in
the operands.

We model the first case by introducing abstraction edges between lifetime
projections in the operands and those in the result place: each lifetime
projection in the operands is connected to the corresponding lifetime
projections that it outlives in the result place. The (compiler-checked)
outlives constraint captures whether borrows could be assigned in this way,
according to the type system.

For (2) To directly model the potentially changed sets of borrows relevant to
these concerns, our analysis of function calls introduces lifetime projections
to represent the post-state of each lifetime projection in the operands. Each
lifetime projection in the operands is connected with abstraction edges to its
corresponding post-state projection as well as the post-state nested lifetime
projections that it outlives (analogously to sets of borrows explicitly
returned).

## Creating Function Shapes

### Function Shapes

A _function shape source base_ $B_S$ takes the form $\text{arg}~i$. A function
shape _target base_ $B_T$ is either $\text{arg}~i$ or $\text{result}$.

A _function shape source node_ $N_B$ is a pair $\langle B_S, i \rangle$ where
$i$ is the _region index_ of the node. _Function shape target nodes_ $N_T$ are defined
analogously.

A _function shape edge_ is a pair $\langle N_B,~ N_T \rangle$, and a
_function shape_ $S$ is a set of edges.

A shape $S$ _permits more borrowing_ than a shape $S'$ iff $S' \subseteq S$;
likewise $S$ _permits less borrowing_ than $S'$ iff $S \subseteq S'$.

### Signature Shape

The _corresponding node_ $n(\glproj)$ of a generalized lifetime projection $\glproj \in \glprojs(\funcinst{f})$ is  $\langle \lpbase{rp},~\lpindex{rp} \rangle$.

The _corresponding generalized lifetime projection_ $\glproj(n)$ of a node $n = \langle b,~i \rangle$ is the generalized lifetime projection $\glproj \in \glprojs(\funcinst{f})$ such that $n(\glproj) = n$.

A generalized lifetime $\glft$ _outlives_ a generalized lifetime $\glft'$ in the signature of $\funcinst{f}$ (denoted $\funcinst{f} \vdash \glft : \glft'$ iff:

- $\glft = \glft'$, or
- $\glft$ is a generalized type $\gty$ and $\glft'$ is a region $\region'$ and
$\paramenv(\funcinst{f}) \vdash \glft : \region'$

Note that $\regionsin{\ty}$ represents _all_ regions that could occur in
$\ty$. More generally, $\regionsin{\ty}$ outlives $\regionsin{\ty'}$ when
all regions in $\ty$ outlive all _corresponding_ regions in $\ty'$. The current
implementation handles the case where $\ty = \ty'$ (reflexivity); other cases
may be added in the future.

<!--

##### Trait-bound region extraction

When extracting generalized lifetimes from a function signature, regions from
trait bounds of type parameters are included as separate lifetime projections.
For a type parameter $\ty$ with bound $\ty : \text{Foo}\langle r \rangle$, the
generalized lifetimes for $\ty$ include both $\regionsin{\ty}$ and
$\text{Region}(r)$. This allows the signature shape to track individual
trait-bound regions and establish fine-grained outlives relationships.

Trait-bound regions inherit invariance from their associated type parameter:
if $\ty$ appears in an invariant position (e.g. under a mutable reference),
its trait-bound regions are also considered invariant.

#### Implementation: `generalized_outlives`

The outlives relation for generalized lifetimes is implemented by the
`generalized_outlives` function in `abstraction/function.rs`. It determines
whether `sup` outlives `sub` by computing reachability in a directed graph whose
nodes are generalized lifetimes and whose edges are derived from the parameter
environment and function signature.

##### Pre-computed data

Before the search begins, two data structures are built:

1. **Trait bound regions** (`TraitBoundRegions`): For each type parameter or
   alias type $\ty$ appearing as the `Self` type of a trait bound in the param
   env (e.g. $\ty : \text{Foo}\langle r_1, r_2\rangle$), the regions appearing in the
   non-self arguments of the trait bound are collected. This produces a map
   $\ty \mapsto \{r_1, \ldots, r_n\}$. These regions are used to create
   additional lifetime projections for the function signature (see
   [Trait-bound region extraction](#trait-bound-region-extraction)), but do
   **not** produce edges in the outlives graph. The bound
   $\ty : \text{Foo}\langle r \rangle$ does not imply $\ty : r$ (not all
   regions in $\ty$ need outlive $r$), nor does it imply that $r$ is a region
   "in" $\ty$.

2. **Implied type-outlives bounds**: For reference types $\texttt{\&}r~\ty$ or
   $\texttt{\&}r~\texttt{mut}~\ty$ occurring in the function's input types,
   well-formedness implies $\ty : r$. These implied bounds are collected
   recursively through ADTs and tuples, and recorded for type parameters and
   non-normalizable alias types.

##### Graph edges

The graph has three kinds of edges:

1. **Region $\Rightarrow$ Region**: From the free-region map, which encodes
   explicit outlives bounds like $r : r'$. These edges are checked _after_ the
   BFS completes (see below).

2. **$\regionsin{\ty} \Rightarrow \text{Region}(r)$**: If any of the
   following hold:
   - There is an explicit $\ty : r$ type-outlives clause in the param env.
   - An implied bound $\ty : r$ was derived from a reference type in the
     signature (e.g. from $\texttt{\&}r~\ty$).
   - $r$ appears directly in $\ty$ itself (e.g. if $\ty$ is $A\langle r \rangle$ after
     substitution of a type parameter).

3. **$\regionsin{\ty} \Rightarrow \regionsin{\ty}$**: Reflexivity —
   since $\regionsin{\ty}$ represents all regions in $\ty$, it trivially
   outlives itself. This is handled by the equality check in the BFS.

Trait bounds like $\ty : \text{Foo}\langle r \rangle$ do **not** produce edges
in either direction: they do not imply $\ty : r$ (so no
$\regionsin{\ty} \Rightarrow \text{Region}(r)$), nor that $r$ is a
region "in" $\ty$ (so no $\text{Region}(r) \Rightarrow
\regionsin{\ty}$).

There is also no general $\text{Region}(r) \Rightarrow \regionsin{\ty}$
edge: just because $r$ outlives some region in $\ty$ does not mean $r$ outlives
_all_ regions in $\ty$ (unless $r$ is $\texttt{'static}$).

##### BFS reachability

The function performs a breadth-first search starting from `sup`:

- At each node, if the current node equals `sub`, return `true`.
- For a $\text{Region}(r)$ node: no outgoing edges in the BFS (Region →
  Region edges are handled after the BFS via the free-region map).
- For a $\regionsin{\ty}$ node: follow edges of kind 2 — enqueue
  $\text{Region}(r)$ for each $r$ reachable from $\ty$ via explicit
  type-outlives clauses, implied bounds, or regions appearing in $\ty$
  itself.

After the BFS exhausts the queue, if $\text{sub}$ was not reached directly, a final
check handles **Region → Region** edges: if $\text{sub}$ is a $\text{Region}(r_{\text{sub}})$,
the function checks whether any visited $\text{Region}(r)$ satisfies $r$ outlives
$r_{\text{sub}}$ according to the free-region map (or if $r$ is $\texttt{'static}$).
This deferred handling avoids expanding the full free-region relation during the
BFS itself.

##### Example

Consider a function with signature:

```rust
fn f<'a, 'b, T: Foo<'a>>(x: &'b T) -> &'a U
where T: 'a, 'b: 'a
```

The pre-computed data contains:
- Trait bound regions: $T \mapsto \{\texttt{'a}\}$ (from $T : \text{Foo}\langle\texttt{'a}\rangle$)
- Implied type-outlives: $T \mapsto \{\texttt{'b}\}$ (from $\texttt{\&'b}~T$)

To check whether $\regionsin{T}$ outlives $\texttt{'a}$:
1. Start BFS at $\regionsin{T}$.
2. From $\regionsin{T}$, follow edges to $\text{Region}(\texttt{'a})$
   (explicit $T : \texttt{'a}$ clause in the param env)
   and $\text{Region}(\texttt{'b})$ (implied bound from $\texttt{\&'b}~T$).
3. $\text{Region}(\texttt{'a})$ matches the target — return `true`.

Note that the trait bound $T : \text{Foo}\langle\texttt{'a}\rangle$ does **not**
contribute to this result — the $\regionsin{T} \Rightarrow
\text{Region}(\texttt{'a})$ edge comes from the explicit $T : \texttt{'a}$
clause, not from the trait bound.

-->

The _signature shape_ $\defn{sigshape}{\sigshape{\funcinst{f}}}$ for a function instantiation $\funcinst{f}$ is defined as follows:

For each $\langle \lproj{b_s}{\glft{}_s}, \lproj{b_t}{\glft{}_t} \rangle \in \glprojs(\funcinst{f}) \times \glprojs(\funcinst{f})$ then add
$\langle{n(\lproj{b_s}{\glft_s}), n(\lproj{b_t}{\glft_t} \rangle)\rangle}$ to $\sigshape{\funcinst{f}}$ if both:

1. $\funcinst{f} \vdash \glft_s: ~\glft_t$, and
2. $b_t$ is $\text{result}$, or $\glft_s$ is a region $r$ that is invariant in $b_t$.

### Call Shape

The _corresponding node_ $n(rp)$ of a lifetime projection $\lproj{op}{r} \in RP(\fncall)$ is
 $\langle \text{arg}~i, \lpindex{rp} \rangle$.

The _corresponding node_ $n(rp)$ of a lifetime projection $\lproj{p}{r} \in RP(\fncall)$ is
 $\langle \text{result}, \lpindex{rp} \rangle$.

$\{\langle \lpbase{rp},~\lpindex{rp} \rangle~|~rp \in RP(\funcinst{f}) \}$

The _call shape_ $\defn{callshape}{\callshape{\fncall}}$ for a function call $\fncall$ is defined as follows:

For each $\langle \lproj{b_s}{r_s}, \lproj{b_t}{r_t} \rangle \in RP(\fncall) \times RP(\fncall)$ then add
$\langle{n(\lproj{b_s}{r_s}), n(\lproj{b_t}{r_t} \rangle)\rangle}$ to $\fshape{\fncall}{call}$ if both:

1. $r_s~\text{outlives}~r_t$ at $l$ according to the borrow checker, and
2. $b_t$ is $p$, or $r_s$ is invariant in $b_t$.

### Type Aliases and Normalization


An _alias type_ $\ty_\alpha$ is a type of the form $\ty::T\langle\overline{\gty}\rangle$ where $T$ is a type constructor. The function $\defn{normalize}{\normalize(\ty, E)}$ returns a type $\ty'$ where alias types in $\ty$ may possibly be replaced with other types. This normalisation is idempotent, e.g. $\normalize(\normalize(\ty, E), E) = \normalize(\ty, E)$.

### Signature-Derived Call Shape

For a call $\fncall = (p = \funcinst{f}(\ops)$ at $l$), the _signature-derived
call shape_ $\sigshape{\fncall}$ is obtained as follows:

Let $\fshape{\funcinst{f}}{norm}$ be the _normalized signature shape_, e.g the one obtained by replacing each $\ty$ in $\sigshape{\funcinst{f}}$ with $\normalize(\ty, \paramenv(\fncall))$.

If $b$ is the $i'th$ operand in $\fncall$, the _corresponding normalized type_
$\ty_b$ is the type of the $i'th$ argument in $\fshape{\funcinst{f}}{norm}$.
Likewise, if $b = \text{result}$, then $\ty_b$ is the output type
of$\fshape{\funcinst{f}}{norm}$. Then, the _corresponding normalized region_ of
a lifetime projection $\lproj{b}{r}$ is the region in $\ty_b$ that corresponds
to $r$ in $b$.

For each $(n_s, n_t) \in \callshape{\fncall}$:
  - Let $\lproj{b_s}{r_s} = rp(n_s)$, $\lproj{b_t}{r_t} = rp(n_t)$ be the corresponding lifetime projections
  - Then, let $r_s'$ and $r_t'$ be the corresponding normalized regions of $r_s$ and $r_t$ respectively.
  - If $r_s'$ outlives $r_t'$ in $\fshape{\funcinst{f}}{norm}$, then add $(n_s, n_t)$
    to $\sigshape{\fncall}$

## Using shapes for function calls in the PCG

If the call is to a defined function, then the signature-derived call shape is
used. Otherwise, the call shape is used.

## More Background

For a function $f$, there are three types of shapes to consider:

- _Signature Shapes_: The shape of an instantiation of $f$ generated from its signature
- _Call Shapes_: A shape used to represent _call_ to an instantiation of $f$
- _Implementation Shapes_: A shape representing $f$'s body, which connects remote lifetime projection nodes to the the result.

These different shape types are relevant for Prusti, as:

- Signature shapes define the shape of a magic wand
- Call shapes are used for magic wands that will be applied
- Implementation shapes define magic wands that will be packaged


The call shape and implementation shapes are necessarily related to the signature shape; the former can contain _more_ edges while the latter can contain _less_.

<!-- We can generate shapes for both function calls, as well as for functions themselves. Generation for calls is performed straightforwardly by identifying the lifetime projections from the inputs and outputs, then querying the borrow-checker for outlives constraints between their corresponding regions. In this case, the base of these lifetime projections are mir places and their regions are always `RegionVid`s. We will call these regions `CallRegion`s. A pair (place, `CallRegion`) is a _Call Projection_.

For a function call, we can, in-principle, generate a shape in a similar matter. For example, a function `fn f<'a, 'b: 'a, 'c>(x: T<'a>, y: U<'b>, z: T<'c>) -> W<'a>` would have edges corresponding to `x|'a -> result|'a` and `y|'b -> result|'a`, with the latter reflecting the outlives constraints from the function signature. In this case, the bases are either $\text{arg}~i$ or `result`, and their regions (I think) early or late-bound lifetime vars, or the `'static` lifetime. We will call these `DefRegion`s. A pair of such a base (argidx or result) and a `DefRegion` is a `Def Projection`. -->

The shape for a function call must necessarily have corresponding edges that appear in the shape for the function signature. The reverse is not necessarily the case. For example, consider the following:

```rust
fn caller<'e, 'f: 'e>(x: T<'e>, y: U<'e>, z: T<'f>) {
    let r: W<'e> = f(x, y, z);
}
```

Using the borrow-checker to generate the shape of the call will result in an edge from `z|'f` to `r|'e`: the borrow-checker reflects that `'f: 'e`. However, the definition of `f`  do not allow borrows to flow from `z` to `r` (which is reflected in the function call shape).

Therefore, to build more precise graphs at function call sites. We want to use the shape of the _function_ to determine the shape of the _call_. The procedure is as follows:

1. Generate the shape of the function.
2. Build a map $M$ from `Def Projection`s to `Call Projections` by comparing the types of the arg places $T_p$ and formal args $T_a$ (analogously to the results). By construction, $M$ will contain all projections in the function def (even if they don't appear in the shape).

Here's an example of how its computed:

If the type of the $i$'th place $T_p$ is `&'?1 mut U<'?2>` and the type of the $i$'th formal arg $T_a$ is `&'a mut U<'b>`, then the visitor will first compare at the top level, add `arg_i |'a -> p_i '?1` to the map and continue by comparing `U<'?2> to U<'b>`

3. Then, for each edge in the fn shape, the edge is replaced with the corresponding projections of the call. If the fn shape has an edge `arg 1|'a -> result|'b` for example, then for the call shape it will lookup corresponding call projections and add an edge between them.

## Reasoning about Associated Types

Consider the following code:

```rust
trait MyTrait<'a> {
    type Assoc<'b> where 'a: 'b;

    fn get_assoc<'slf, 'b>(&'slf mut self) -> Self::Assoc<'b> {
      todo!()
    }
}
```

The full signature for `get_assoc` is:
```rust
fn(&'slf mut Self) -> <Self as MyTrait<'a>>::Assoc<'b>
```

we observe that the fn sig has the following lifetime projections:

- `argidx 0|'slf`
- `result 0|'a`
- `result 0|'b`


And the shape for `get_assoc` contains the single edge:
- `argidx 0|'slf -> result|'b`


For the body, `self` has type `&'8 mut Self/#0`
and `result` has `Alias(Projection, AliasTy { args: [Self/#0, '?6, '?7], def_id: DefId(0:5 ~ input[9b88]::MyTrait::Assoc), .. })`,


So we unify  `&'slf mut Self`  with `&'?8 mut Self`
adding `argidx 0|'slf` -> `_1|'?8` to $M$

We unify `<Self as MyTrait<'a>::Assoc<'b>` with
`<Self as MyTrait<'?6>::Assoc<'?7>`
adding
- `result|'a -> result|'?6` to $M$
- `result|'b -> result|'?7` to $M$

Then applying the substitutions our shape is  `_1|'?8 -> result|'?7`

<!-- ## Implementation

We differentiate shapes for calls and functions at the type level.

We define a `FunctionShape<Type>` -->
