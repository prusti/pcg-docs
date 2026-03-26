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

### Types and Parameter Environments

A _type_ $\tau$ is either:
- A type parameter of the form $\text{param}~i$
- An alias type of the form $\tau::T\langle\overline{\tau}\rangle$
- A _type constructor application_ of the form $T\langle\overline{\tau}\rangle$

A _generalized type_ $\gty$ is either a type $\tau$ or a region $r$

A _param env_ $\paramenv$ is a list of constraints $\overline{\gty : \gty'}$.

#### Corresponding Regions

If $r$ is a region in $\tau$, the _corresponding region_ $r_c$ in a type $\tau_c$ is:

If $\tau = \texttt{\&}~r~m~\tau'$ and $\tau_c = \texttt{\&}~r_c'~m~\tau_c'$ then $r_c = r_c'$

If $\tau = T\langle\tau_1, \ldots, t_n\rangle$  and $\tau_c = T\langle\tau_{c_1}, \ldots, t_{c_n}\rangle$, iterate $i$ over $1, \ldots, n$, and if there exists an $r_c'$ where $r_c'$ in $\tau_{c_i}$ is the corresponding region of $r$ in $t_i$, then $r_c = r_c'$.

### Lifetime Projections

A _generic lifetime_ $\glft$ is either a region $r$ or a type $\tau$, where
$\tau$ is either:
1. a type parameter, or
2. a type alias that cannot be normalized

A _generic lifetime projection_ $\glproj$ takes the form $\lproj{b}{gr}$ where $b$ is a _base_ having an associated type $\tau$. The _index_ $\lpindex{\glproj}$ of a lifetime projection is the index of the occurence of $gr$ in the _generic lifetime list_ $\glfts(\tau)$ (the list of generic lifetimes in $\tau$, occurring in the order they appear in $\tau$, and with duplicates removed).

A _lifetime projection_ is a generic lifetime projection of the form $\lproj{b}{r}$ (that is, a generic lifetime projection where the associated generic lifetime is a region).

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

### Function Signatures

A _function signature_ is a pair $\langle\fargtys,~\fresty\rangle$.

A _defined function signature_ $f$ is a tuple $\langle id, ~\fargtys,~\fresty, \paramenv \rangle$.


An _instantiation_ $\hat{f}$ of $f$ is the tuple $\langle f, \overline{\gty}\rangle$;
where $\gty$ is a list of _early-bound parameters_.
An _instantiation_ $\hat{f}$ of $f$ is the tuple $\langle f, \overline{\gty}\rangle$; the _identity instantiation_ $f_I$ of $f$ is obtained by applying the _identity substitution_ $I_\gty$.  _Defined function calls_ are applied to _instantiations_ of a function.

The _generic lifetime projections_ $\glprojs(\funcinst{f})$ of a function instantiation $\hat{f}$ is defined as the set:

$\{\lproj{\text{arg}~i}{\glft}~|~ i \leqslant |\fargtys|, \glft \in \glfts(\fargty{i})|\} \cup $
$\{\lproj{\text{result}}{\glft}~|~\glft \in \glfts(\fresty)\}$

#### Signature Shape

The _corresponding node_ $n(\glproj)$ of a generic lifetime projection $\glproj \in \glprojs(\funcinst{f})$ is  $\langle \lpbase{rp},~\lpindex{rp} \rangle$.

The _corresponding generic lifetime projection_ $\glproj(n)$ of a node $n = \langle b,~i \rangle$ is the generic lifetime projection $\glproj \in \glprojs(\funcinst{f})$ such that $n(\glproj) = n$.

A generic lifetime $\glft$ _outlives_ a generic lifetime $\glft'$ in the signature of $\funcinst{f}$ iff:

- $\glft = \glft'$, or
- $gr$ is a region $r$ and $gr'$ is a region $r'$ and $r$ outlives $r'$ in $\funcinst{f}$, or
- $gr$ a type $\tau$ and $gr'$ is a type $\tau'$ and $\tau'$ is an associated type of $\tau$.
- $gr$ a type $\tau$ and $gr'$ is a region $r'$ and the constraint $\tau : r'$ holds; i.e. this constraint exists syntactically or $\tau$ outlives some region $r$ where $r$ outlives $r'$

The _signature shape_ $\sigshape{\funcinst{f}}$ for a function instantiation $\funcinst{f}$ is defined as follows:

For each $\langle \lproj{b_s}{\glft{}_s}, \lproj{b_t}{\glft{}_t} \rangle \in \glprojs(\funcinst{f}) \times \glprojs(\funcinst{f})$ then add
$\langle{n(\lproj{b_s}{\glft_s}), n(\lproj{b_t}{\glft_t} \rangle)\rangle}$ to $\sigshape{\funcinst{f}}$ if both:

1. $\glft_t~\text{outlives}~\glft_s$ in the signature of $\funcinst{f}$, and
2. $b_t$ is $\text{result}$, or $\glft_s$ is a region $r$ that is invariant in $b_t$.

<div class="warning">

The above defn does not include edges for e.g. $(\lproj{arg}{T}) \rightarrow (\lproj{arg}{T})$, which presumably should be there in some form for regions in $T$ that are invariant in the type of $\textit{arg}$.

</div>

### Function Calls

A _function call target_ $\tilde{f}$ is either an instantiation $\funcinst{f}$ or a closure / function pointer $ct$.

A _function call_ $FC$ takes the form $p =
\tilde{f}(\overline{op})~\text{at}~l$, where $p$ is a MIR place, and
$\overline{op}$ is a sequence of MIR operands.

The _lifetime projections_ $RP(FC)$ of a function call is the union of the lifetime projections in $p$ and the lifetime projections in $\overline{op}$.

A function call $FC$ is valid iff it satisfies the _unique region property_: each region in the lifetime projections of $FC$ is unique.

<div class="warning">
We assume that function calls generated by directly extracting the result place
and operands from a MIR body are valid.
We note that converting the places to PCG places (which use the type derived from their local), does not necessarily maintain the validity of a function call.
</div>

#### Call Shape

The _corresponding node_ $n(rp)$ of a lifetime projection $\lproj{op}{r} \in RP(FC)$ is
 $\langle \text{arg}~i, \lpindex{rp} \rangle$.

The _corresponding node_ $n(rp)$ of a lifetime projection $\lproj{p}{r} \in RP(FC)$ is
 $\langle \text{result}, \lpindex{rp} \rangle$.

$\{\langle \lpbase{rp},~\lpindex{rp} \rangle~|~rp \in RP(\funcinst{f}) \}$

The _call shape_ $\callshape{FC}$ for a function call $FC$ is defined as follows:

For each $\langle \lproj{b_s}{r_s}, \lproj{b_t}{r_t} \rangle \in RP(FC) \times RP(FC)$ then add
$\langle{n(\lproj{b_s}{r_s}), n(\lproj{b_t}{r_t} \rangle)\rangle}$ to $\fshape{FC}{call}$ if both:

1. $r_t~\text{outlives}~r_s$ at $l$ according to the borrow checker, and
2. $b_t$ is $p$, or $r_s$ is invariant in $b_t$.

### Type Aliases and Normalization


An _alias type_ $\tau_\alpha$ is a type of the form $\tau::T\langle\overline{\gty}\rangle$ where $T$ is a type constructor. The function $\normalize(\tau, E)$ returns a type $\tau'$ where alias types in $\tau$ may possibly be replaced with other types. This normalisation is idempotent, e.g. $\normalize(\normalize(\tau, E), E) = \normalize(\tau, E)$.

### Signature-Derived Call Shape

For a call $FC = (p = \funcinst{f}(\ops)$ at $l$), the _signature-derived
call shape_ $\sigshape{FC}$ is obtained as follows:

Let $\fshape{\funcinst{f}}{norm}$ be the _normalized signature shape_, e.g the one obtained by replacing each $\tau$ in $\sigshape{\funcinst{f}}$ with $\normalize(\tau, \paramenv)$,
where $\paramenv$ is the param env of $f$.

If $b$ is the $i'th$ operand in $FC$, the _corresponding normalized type_
$\tau_b$ is the type of the $i'th$ argument in $\fshape{\funcinst{f}}{norm}$.
Likewise, if $b = \text{result}$, then $\tau_b$ is the output type
of$\fshape{\funcinst{f}}{norm}$. Then, the _corresponding normalized region_ of
a lifetime projection $\lproj{b}{r}$ is the region in $\tau_b$ that corresponds
to $r$ in $b$.

For each $(n_s, n_t) \in \callshape{FC}$:
  - Let $\lproj{b_s}{r_s} = rp(n_s)$, $\lproj{b_t}{r_t} = rp(n_t)$ be the corresponding lifetime projections
  - Then, let $r_s'$ and $r_t'$ be the corresponding normalized regions of $r_s$ and $r_t$ respectively.
  - If $r_s'$ outlives $r_t'$ in $\fshape{\funcinst{f}}{norm}$, then add $(n_s, n_t)$
    to $\sigshape{FC}$

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
