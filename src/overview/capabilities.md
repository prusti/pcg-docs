# Capabilities

There are four types of capabilites:

## Exclusive (`E`)

Places with this capability can be read from, written to, or mutably borrowed.

We do not differentiate between locals bound with `let` bindings and `let mut`
bindings: a variable bound with `let` would still have this capability if it
could be written to if it was mutably borrowed.

## Read (`R`)

Places with this capability can be read from. Shared borrows can also be created
to this place. Shared references with this capability can be dereferenced.

A place $p$ with capability `E` is downgraded to `R` if a shared borrow is
created to a place that is a pre- or postfix of $p$.

When a shared reference $p$ is dereferenced, the capability to $p$ is downgraded
to `R`. Any place projecting from a shared references will have capability `R`.

## Write (`W`)

The place can be written to.

When an exclusive reference $p$ is dereferenced, the capability to $p$ is downgraded
to `W`.

## ShallowExclusive (`e`)

This is used for a rather specific and uncommon situation. When converting a raw
pointer `*mut T` into a `Box<T>`, there is an intermediate state where the
memory for the box is allocated on the heap but the box does not yet hold a
value. We use `ShallowExclusive` to represent this state.

Writing to a Box-typed place `p` via e.g. `*p = 5` requires that `p` have
capability `e`.
