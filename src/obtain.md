# Obtain

We "obtain" a capability $c$ to a place $p$ by rewriting the PCG into a state in which $p$ has capability $c$.
Note that a place node for $p$ is not necessarily present in the graph before this occurs.
This proceeds as follows:

### Step 1 - Upgrading Closest Ancestor From R to E
First, if the capability we seek to obtain is $W$ or $E$ and the *closest ancestor* $q$ to $p$, that is, the longest prefix of $p$ for which there exists a node in the graph, has $R$ capability, we upgrade $q$'s capability to $E$ by removing capability from $q$'s parent (if it exists).

### Step 2 - Restoring Unpacked Capabilities
Then, if a node for $p$ exists in the graph and $p$'s capability is not at least as strong as $c$, we iteratively pack up the projections of $p$ in reverse topological order, with the effect of flowing capabilities back to $p$.
Simultaneously, when we pack the expansions of a node $q$, for each lifetime $'a$ of $q$'s type, we create a lifetime projection node $q\downarrow~'a$ and insert an edge $\{r\downarrow~'a\} \rightarrow \{q\downarrow~'a\}$ for each lifetime projection node $\{r\downarrow~'a\}

- for each lifetime projection in x, look in the children for the same lifetime...

- every expansion region projection node's PLACE gets labelled with "before"
- lifetime projections for all the places that need to get packed up into the base are redirected to the new base lifetime projection

### Step 3 - Labelling Lifetime Projections
At this point, if $c$ is $W$, we know that a subsequent operation will mutate $p$.
As a result, if there exists a lifetime projection node for $p$ (for example, if $p$ stores a borrow that has since been reborrowed), it will no longer be tied to the current value of $p$.
So, we label the lifetime projection as "old" using the current program point.

### Step 4 - Expand
If there is still no node for $p$ in the graph, we iteratively unpack the prefixes of $p$ (and their associated region projections) in increasing order of length until $p$ exists in the graph with capability $c$.

### Step 5 - Labelling Lifetime Projections for Projections
Finally, if we are obtaining $W$ or $E$ capability, we can again assume that the intention is to mutate $p$.
If there exist any lifetime projection nodes for dereferences of $p$'s fields (or $p$'s fields' fields, and so on...), we encounter the same problem that was described in Step 3.
To address this, we label any lifetime projections for dereferences of places *for which $p$ is a prefix* (`*p.f`, for example) as "old" using the current program point.
