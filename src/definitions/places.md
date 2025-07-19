# Places

A place $p$ is a tuple of a local $\local$ and a projection.

## Place Expansion

<div class="warning">
This is missing some cases
</div>

A set of places $\overline{p}$ is an *expansion* of a place *p* iff:
- $p$ is an `enum` type and $\overline{p} = \{p~\mathtt{@}~V\}$ and $V$ is a variant of $p$
- $p$ is a `struct` or tuple type and $\overline{p}$ is the set of places obtained by projecting $p$ with each of the fields in the type of $p$
- $p$ is a reference-typed field and $\overline{p} = \{*p\}$
- $p$ is an array or slice and $\overline{p} = p[i]$ (TODO: more cases)

## Owned Places

A place is *owned* iff it does not project from the dereference of a
reference-typed place.

## Place Liveness

A place $p$ is live at a location $l$ iff there exists a location $l'$ and a control flow-path $c$ from $l$ to $l'$ where a place *conflicting with* $p$ is used at $l'$ and there are no assignments of any places *conflicting with* $p$ along c.

## Place Prefix

A place $p$ is a *prefix* of a place $p'$ iff:
- $p$ and $p'$ have the same local, and
- The projection of $p$ is a prefix of the projection of $p'$

Note that $p$ is a prefix of itself.

A place $p$ is a *strict prefix* of $p'$ iff $p$ is a prefix of $p'$ and $p \neq p'$.
