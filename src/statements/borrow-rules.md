# Rules for the Creation of Borrows

## Mutable Borrows

Consider the stmt `p = &mut q`, at a program point $l$, where $p$ has type $\&r_0 ~\mathtt{mut}~\tau$, and $q$ has type $\tau$, and $\tau$ is a type containing lifetimes $r_1, \ldots r_n$.

At the end of the `PreOperands` phase, the PCG is guaranteed to be in a state where, for each $r_i \in \{r_1, \ldots, r_n\}$ the lifetime projection $q \downarrow r_i$ is in the graph. During the `Operands` phase, each lifetime projection $q \downarrow r_i$ is *labelled* with the current program point to become $q \downarrow r_i ~\mathtt{at}~l$. At the end of the `PreMain` phase, for each $r_i \in \{r_0, \ldots, r_n\}$, the lifetime projection $p\downarrow r_i$ is guaranteed *not* to be in the graph. During the `Main` phase, these projections are added.

Subsequently, the labelled lifetime projections under $p$ are connected with `BorrowFlow` edges to the new lifetime projections under $q$. Namely, for each $i \in \{1, \ldots n\}, j \in \{0, \ldots, n\}$ if $r_i$ outlives $r_j$, then a `BorrowFlow` edge $\{q \downarrow r_i~\mathtt{at}~l\} \rightarrow \{p \downarrow r_j\}$ is added.

Subsequently, we introduce `Future` nodes and edges to account for nested references as follows. For each $i \in \{1, \ldots n\}$:

1. Insert the node $q \downarrow r_i~\mathtt{at Future}$ into the graph
2. If any `Future` edges originate from the labelled projection $q \downarrow r_i~\mathtt{at}~l$, redirect  them such that they originate from $q \downarrow r_i~\mathtt{at Future}$.
3. Insert a `Future` edge $\{q \downarrow r_i~\mathtt{at}~l\} \rightarrow \{q \downarrow r_i~\mathtt{at Future}\}$
4. Insert a `Future` edge $\{p \downarrow r_i\} \rightarrow \{q \downarrow r_i~\mathtt{at Future}\}$
