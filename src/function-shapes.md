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

A function shape _source base_ $B_S$ takes the form $\text{arg}~i$. A function
shape _target base_ $B_T$ is either $\text{arg}~i$ or $\text{result}$.  A
function shape _source node_ $N_B$ is a pair $\langle B_S, i \rangle$ where $i$ is
the _region index_ of the node. Target nodes $N_T$ are defined analogously. A
_function shape edge_ $E$ is a pair $\langle N_B,~ N_T \rangle$ and a _function
shape_ $S$ is a set of edges.

A shape $S$ _permits more borrowing_ than a shape $S'$ iff $S' \subseteq S$;
likewise $S$ _permits less borrowing_ than $S'$ iff $S \subseteq S'$.

### Borrow-Flow Relation

A borrow-flow relation $F$ is a binary relation relating source nodes to target
nodes; the _implied shape_ of the relation contains one edge for each

The _implied shape_ of a borrow-flow relation $F$ is the shape $S$ where $\langle n_s, n_t \rangle \in S$ iff $(n_s, n_t) \in F$.

### Functions

A function $f$ is parameterized by a list of _early-bound args_ $E$ and _late-bound parameters_ $L$. An _instantiation_ $\hat{f}$ of $f$ is the tuple $\langle f, E, L \rangle$; the _identity instantiation_ $f_I$ of $f$ is obtained by applying the _identity substitutions_ $I_E$ and $I_L$.  Function calls are applied to _instantiations_ of a function.

### Function Definition Borrow-Flow Relation

The _function definition borrow-flow relation_ $\bfrel{\funcinst{f}}{def}$ for a function instantiation $\funcinst{f}$ is defined as follows:

The region $r(n)$ of a node $n = \pair{a}{i}$ the $i'th$ region of the arg / result $a$.
Then, $\pairp{n_s}{n_t} \in \bfrel{\funcinst{f}}{def}$ iff:

1. $r(n)~\text{outlives}~r(n')$ in the signature of $\funcinst{f}$.
2. $base(n_t)$ is $\text{result}$, or $r(n)$ is invariant in the $i'th$ type

### Function Call Borrow-Flow Relation

For a function call $FC = \funcinst{f}(\overline{p})~\text{at}~l$,
the _function call borrowflow relation_ $\bfrel{FC}{call}$ is:

The region $r(n)$ of a node $n = \pair{a}{i}$ the $i'th$ region of the arg / result $a$.

Then, $\pairp{n_s}{n_t} \in \bfrel{\funcinst{f}}{call}$ iff

1. $r(n)~\text{outlives}~r(n')$ at $l$ according to the borrow-checker.
2. $base(n_t)$ is $\text{result}$, or $r(n)$ is invariant in the $i'th$ type

### Definition-Derived Call Shape

For a call $FC = \funcinst{f}(\overline{p})$ at $l$, the _definition-derived
borrow-flow relation_ $\bfrel{FC}{def}$

### Function Shape Types

For a function $f$, there are three types of shapes to consider:

- _Definition Shapes_: The shape of an instantiation of $f$ generated from its signature
- _Call Shapes_: A shape used to represent _call_ to an instantiation of $f$
- _Implementation Shapes_: A shape representing $f$'s body, which connects remote lifetime projection nodes to the the result.

These different shape types are relevant for Prusti, as:

- Definition shapes define the shape of a magic wand
- Call shapes are used for magic wands that will be applied
- Implementation shapes define magic wands that will be packaged


The call shape and implementation shapes are necessarily related to the definition shape; the former can contain _more_ edges while the latter can contain _less_.

For example, in Prusti, the _definition shape_


We can generate shapes for both function calls, as well as for functions themselves. Generation for calls is performed straightforwardly by identifying the lifetime projections from the inputs and outputs, then querying the borrow-checker for outlives constraints between their corresponding regions. In this case, the base of these lifetime projections are mir places and their regions are always `RegionVid`s. We will call these regions `CallRegion`s. A pair (place, `CallRegion`) is a _Call Projection_.

For a function call, we can, in-principle, generate a shape in a similar matter. For example, a function `fn f<'a, 'b: 'a, 'c>(x: T<'a>, y: U<'b>, z: T<'c>) -> W<'a>` would have edges corresponding to `x|'a -> result|'a` and `y|'b -> result|'a`, with the latter reflecting the outlives constraints from the function signature. In this case, the bases are either $\text{arg}~i$ or `result`, and their regions (I think) early or late-bound lifetime vars, or the `'static` lifetime. We will call these `DefRegion`s. A pair of such a base (argidx or result) and a `DefRegion` is a `Def Projection`.


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

## Implementation

We differentiate shapes for calls and functions at the type level.

We define a `FunctionShape<Type>`
