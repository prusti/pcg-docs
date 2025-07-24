# Borrow-Checker Interface

The PCG Analysis requires an implementation of the *borrow-checker interface*
providing the following:

- A predicate $\mathit{live}(n, l)$, which holds iff the borrow extents in PCG
  node $n$ are all in scope at MIR location $l$
- A predicate $\mathit{directly\_blocked}(p, l)$, which holds iff place $p$ is
  *directly* blocked at MIR location $l$
- A predicate $\mathit{blocks}(p, p', l)$ which holds iff mutating $p'$ at $l$
  would cause $p$ to be dead
- A predicate $\mathit{outlives}(r, r', l)$ which holds iff $r$ must outlive $r'$ at $l$
- A function $\mathit{borrows\_blocking}(p, l)$ which returns the set of borrows that would be invalidated if $p$ was modified at $l$
- A function $\mathit{twophase\_borrow\_activations}(l)$ which returns the set of two-phase borrows that are activated at $l$.
