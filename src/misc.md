# Misc (To Update)

## Unpacking Places

An *unpack* operation introduces an `Unpack` edge into the graph, and is associated with a *source place* $p$ and an *expansion* $\overline{p}$. An unpack operation can either be *mutable* or *read-only*.

An unpack operation is a *dereference* unpack for lifetime $r$ iff the type of the source place *p* is `&'r mut p` or `&'r p`.

Applying an unpack operation introduces an `Unpack` edge as follows:

1. If the unpack operation is a dereference operation, the edge $\{p, p \downarrow r\} \rightarrow \{*p\}$ is added to the graph.
2. Otherwise, the edge $\{p\} \rightarrow \{\overline{p}\}$ is added to the graph.

A *mutable* unpack operation for capabiliy $c \in \{W, E\}$ requires that the source place $p$ have capability $c$. When the operation is a applied, the capability for $p$ is removed and the capability of all places in $\overline{p}$ is set to $c$.

A *read-only* unpack operation requires that $p$ have capability $R$ and assigns capability $R$ to all places in $\overline{p}$.

### Updating Lifetime Projections

Assume the source place $p$ has type $\tau$ with lifetimes $r_1, \ldots, r_n$. If the unpack operation is mutable, then we label each lifetime projection $p\downarrow r_i$ with location $l$.

The *source* lifetime projection for a lifetime $r$ is $p \downarrow r~\mathtt{at}~l$ if the unpack is mutable, and $p\downarrow r$ otherwise. The *target* lifetime projections is the set $\{p' \downarrow r~|~p' \in \overline p~\text{and}~r~\text{is in the type of}~p'\}$.

For each lifetime $r \in \{r_1, \ldots, r_n\}$, if the set of target lifetime projections associated with $r$ is nonempty:

1. For each $t$ in the set of target projections, add a `BorrowFlow` edge $\{s\} \rightarrow \{t\}$ where $s$ is the source projection[^todo].

[^todo]: **TODO**: Currently we actually introduce an unpack edge in the implementation, but we should change this.

2. If the unpack is mutable and the source place of the expansion is either a reference or a borrowed place:
a. Add a `Future` edge $\{s\} \rightarrow \{p \downarrow r~\mathtt{at Future}\}$
b. For each $t$ in the set of target projections, add a `Future` edge $\{t\} \rightarrow \{p \downarrow r~\mathtt{at Future}\}$
c. If any `Future` edges originate from the source projection $s$, redirect  them such that they originate from $p \downarrow r~\mathtt{at Future}$.

## Origin Containg Loan

An origin $r$ contains a loan $r_L$ created at location $l$ iff:

**Polonius**: Read directly from output facts

**NLL**: $r_L$ is live at $l$ and $r_L$ outlives $l$
