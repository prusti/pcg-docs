# Definitions

## Blocking

A lifetime projection $p\downarrow~r$ *blocks* a place $p_b$ at a location $l$ iff:

- there is a loan $p' = \mathtt{\&mut}~p_b'$ with lifetime $r_L$
- the place $p_b'$ *conflicts* with $p_b$
- $r$ contains $r_L$ at $l$


A place $p$ *blocks* a place $p_b$ at a location $l$ iff it has an associated lifetime projection $p\downarrow~r$ that blocks $p_b$.

If a node $n$ blocks a place $p_b$, then $n$ also blocks all associated lifetime projections of $p_b$.

<div class="info">
ZG: The rules for NLL are based on the implementation in the rust_borrowck crate.

The rules for Polonius are based on the blog post description.
</div>

<div class="info">
Note that the rules for a place $p$ blocking a place $p_b$ only consider the lifetimes in the type of $p$, and do not consider its relation to the original assigned place $p'$ borrowing $p_b$. This is intentional (for example, $p$ could block $p_b$ due to the original assigned place $p'$ being moved into $p$).
</div>
