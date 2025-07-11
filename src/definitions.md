# Definitions

## Blocking

A place $p_{blocker}$ *blocks* a place $p_{blocked}$ at a location $l$ if a
usage of $p_{blocked}$ at $l$ would invalidate a live borrow $b$ contained in the origins of $p_{blocker}$ at $l$.

## Place Liveness

A place $p$ is live at a location $l$ iff there exists a location $l'$ and a control flow-path $c$ from $l$ to $l'$ where a place *conflicting with* $p$ is used at $l'$ and there are no assignments of any places *conflicting with* $p$ along c.

## Borrow Liveness

A borrow $p = \&\texttt{mut}~p'$ is *live* at location $l$ if a usage of $p'$ at
$l$ would invalidate the borrow.

## Directly Borrowed

A place $p$ is *directly borrowed* by a borrow $b$ if $p$ is exactly the borrowed place (not e.g. a pre- or postfix of the place).
