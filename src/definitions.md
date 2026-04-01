# Definitions

## Types

### Type Contains

A type $\ty$ *contains* a type $\ty'$, iff:

1. $\ty = \ty'$, or
2. $\ty$ is an ADT and contains a field $\mathtt{f}: \ty_\mathtt{f}$ and $\ty_\mathtt{f}$ contains $\ty'$
3. $\ty = \mathtt{\&'r~mut}~\ty_{\text{tgt}}$ and $\ty_{\text{tgt}}$ contains $\ty'$

### Types Containing Lifetimes

A type $\ty$ *contains* a lifetime $r$ iff $\ty$ contains the type
$\mathtt{\&\tick{r}~mut}~\ty'$ for some type $\ty'$. A lifetime $r$ is *nested*
in a type $\ty$ iff $\ty$ contains a type $\mathtt{\&'r~mut}~\ty'$ and $\ty'$ contains $r$.
We extend these concept to places: a place $p: \ty$ contains a lifetime $r$ iff
$\ty$ contains $r$; $r$ is nested in $p: \ty$ iff $r$ is nested in $\ty$. A lifetime
projection $p \downarrow r$ is *nested* if $r$ is nested in $p$.

---

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
