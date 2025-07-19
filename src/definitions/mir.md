# MIR Definitions

Here we describe definitions of MIR concepts that are relevant to the PCG.

<div class="warning">

It's possible that these definitions will become outdated as the MIR is not
stable. If there is any discrepency between the descriptions here and those from
official Rust sources (e.g. the [dev guide](https://rustc-dev-guide.rust-lang.org/)), this page should be updated accordingly.

</div>

## MIR Dataflow Analysis

At a high
level, a MIR dataflow analysis is defined by the following elements:
- A *domain* $\mathcal{D}$
- A *join operation* $\mathit{join}: (\mathcal{D} \times \mathcal{D}) \rightarrow \mathcal{D}$
- An *empty state* $d_\epsilon \in \mathcal{D}$
- A *transfer function* $\mathit{transfer}: (\mathcal{D} \times \mathit{Location}) \rightarrow \mathcal{D}$

Performing the dataflow analysis on a MIR body $B$ computes a value of type
$\mathcal{D}$ for every location in $B$. The analysis is performed (conceptually) as follows[^dataflowimpl]:

[^dataflowimpl]: The current analysis implementation (defined in the rust
    compiler) is more efficient than what we describe because it tracks state
    per basic block rather than per-location, as the states for any location in
    a block can be computed by repeated application of the transfer function to
    the entry state.

- The analysis defines a map $S$ that maps locations in $B$ to elements of $\mathcal{D}$.
- Each location in $S$ is initialized to $\mathcal{d}_\epsilon$
- The operation *analyze(b)* updates $S$ as follows:
    - $s[b[0]] \leftarrow \mathit{transfer}(s[b[0]], b[0])$
    - For $0 < i  \leqslant |b|: s[b[i]] \leftarrow \mathit{transfer}(s[b[i -1]], b[i])$
- The analysis defines a worklist $W = [b_0]$
- While $W$ is not empty:
    - Pop $b$ from $W$
    - Perform $analyze(b)$
    - Let $s_b^\mathit{exit}$ be the entry of the last location in $b$ in $s$
    - For each successor $b'$ of $b$:
        - Let $s_{b'}^{\mathit{entry}} = s[b'[0]]$
        - Let $s_{b'}^{\mathit{join}} = \mathit{join(s_{b'}^{\mathit{entry}}, s_b^{\mathit{exit}})}$
        - If $s_{b'}^{\mathit{join}} \neq s_{b'}^{\mathit{entry}}$:
            - $s[b'[0]] \leftarrow s_{b'}^{\mathit{join}}$
            - Add $b'$ to $W$
- $S$ is the result

<div class="warning">

I'm not sure of the order things are popped from $W$. Any ordering should yield
the same $S$ but some blocks may be analyzed more frequently than necessary. We
should check the rustc implementation.

</div>
