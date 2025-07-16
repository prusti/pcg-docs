# Obtain

We "obtain" a capability $c$ to a place $p$ by rewriting the PCG into a state in which $p$ has capability $c$.
Note that a place node for $p$ is not necessarily present in the graph before this occurs.
This proceeds as follows:

### Step 1 - Upgrading Closest Ancestor From R to E
First, if the capability we seek to obtain is $W$ or $E$ and the *closest ancestor* $p'$ to $p$, that is, the longest prefix of $p$ for which there exists a node in the graph, has $R$ capability, we upgrade $p'$'s capability to $E$ by removing capability from $p'$'s parent (if it exists).

### Step 2 - Restoring Capability to Ancestor
Then, if a node for $p$ exists in the graph and $p$'s capability is not at least as strong as $c$, we iteratively pack up the projections of $p$ in reverse topological order, with the effect of flowing capabilities back to $p$.

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
