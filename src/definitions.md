# Definitions

## Types

### Type Contains

A type $\tau$ *contains* a type $\tau'$, iff:

1. $\tau = \tau'$, or
2. $\tau$ is an ADT and contains a field $\mathtt{f}: \tau_\mathtt{f}$ and $\tau_\mathtt{f}$ contains $\tau'$
3. $\tau = \mathtt{\&'r~mut}~\tau_{\text{tgt}}$ and $\tau_{\text{tgt}}$ contains $\tau'$

### Types Containing Lifetimes

A type $\tau$ *contains* a lifetime $r$ iff $\tau$ contains the type
$\mathtt{\&\tick{r}~mut}~\tau'$ for some type $\tau'$. A lifetime $r$ is *nested*
in a type $\tau$ iff $\tau$ contains a type $\mathtt{\&'r~mut}~\tau'$ and $\tau'$ contains $r$.
We extend these concept to places: a place $p: \tau$ contains a lifetime $r$ iff
$\tau$ contains $r$; $r$ is nested in $p: \tau$ iff $r$ is nested in $\tau$. A lifetime
projection $p \downarrow r$ is *nested* if $r$ is nested in $p$.

---

## Places

### Place Expansion

<div class="warning">
This is missing some cases
</div>

A set of places $\overline{p}$ is an *expansion* of a place *p* iff:
- $p$ is an `enum` type and $\overline{p} = \{p~\mathtt{@}~V\}$ and $V$ is a variant of $p$
- $p$ is a `struct` or tuple type and $\overline{p}$ is the set of places obtained by projecting $p$ with each of the fields in the type of $p$
- $p$ is a reference-typed field and $\overline{p} = \{*p\}$
- $p$ is an array or slice and $\overline{p} = p[i]$ (TODO: more cases)

### Owned Places

A place is *owned* iff it does not project from the dereference of a
reference-typed place.

### Place Liveness

A place $p$ is live at a location $l$ iff there exists a location $l'$ and a control flow-path $c$ from $l$ to $l'$ where a place *conflicting with* $p$ is used at $l'$ and there are no assignments of any places *conflicting with* $p$ along c.

## PCG Evaluation Phase

The PCG Evaluation Phases are:

- `PreOperands`
- `PostOperands`
- `PreMain`
- `PostMain`

For every MIR location, a seperate PCG is generated for each phase. They represent the following:

- `PreOperands` - A reorganization of the initial state[^initial] to prepare to apply the effects of evaluating the operands in the statement
- `PostOperands` - The result of applying the operand effects on the `PreOperands` state
- `PreMain` - A reorganization of the `PostOperands` state to prepare to apply any other effects of the statement
- `PostMain` - The result of applying any other effects of the statement to the `PreMain` state.
[^initial]: The initial state is either the `PostMain` of the previous location within the basic block. Or if this is the first statement within the block, it is the entry state of the block (i.e. the result from joining the final states of incoming basic blocks).

## Program Point

A program point represents a point within the execution of a Rust function in a
way that is more fine-grained than a MIR location (each MIR location has
multiple program points which to different stages of evaluation of a statement).
Concretely, a program point is either:
- The start of a basic block
- A pair of a MIR location and a PCG evaluation phase

## Borrows and Blocking

### Blocking

A place $p_{blocker}$ *blocks* a place $p_{blocked}$ at a location $l$ if a
usage of $p_{blocked}$ at $l$ would invalidate a live borrow $b$ contained in the origins of $p_{blocker}$ at $l$.


### Borrow Liveness

A borrow $p = \&\texttt{mut}~p'$ is *live* at location $l$ if a usage of $p'$ at
$l$ would invalidate the borrow.

### Directly Borrowed

A place $p$ is *directly borrowed* by a borrow $b$ if $p$ is exactly the borrowed place (not e.g. a pre- or postfix of the place).
