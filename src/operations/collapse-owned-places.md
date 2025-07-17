# Collapsing Owned Places

At the outset of each program point, the *collapse_owned_places* operation eagerly collapses the _Owned PCG_.

It is implemented as follows:

- For each place $p$ for which there exists a place node (from longest to shortest):
  - If no expansion of $p$ is blocked by a borrow and every expansion of $p$ has the same capability:
    - perform the [*collapse(p)*](./obtain.html#collapse) operation
    - if $p$ has no projection and has $R$ capability, upgrade $p$'s capability to $E$
