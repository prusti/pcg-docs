# Activating Two-Phase Borrows

#### *activateTwophaseBorrowCreatedAt*
*reserveLocation* is a function from borrow edges to the MIR location at which the borrow edge was created.

The *activateTwophaseBorrowCreatedAt* operation takes a single parameter:

- $l$, a MIR location

The operation is implemented as follows:
- If there exists a borrow edge $e = \{ p \} \rightarrow ps$ in the graph such that *l = reserveLocation(e)*:
  - If there exists a place node for $*p$ in the graph:
    - Restore $E$ capability to $*p$ 
  - If $p$ is not owned:
    - Downgrade the capability of every ancestor of $p$ to None
- TODO Logic is bad
