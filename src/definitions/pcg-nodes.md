# PCG Nodes

$$
\newcommand{\bb}{\mathtt{bb}}          % Basic blocks
\newcommand{\ppointbefore}[1]{{\text{before}~#1}}
\newcommand{\ppointafter}[1]{{\text{after}~#1}}
\newcommand{\ppoint}{{l}}
\newcommand{\location}{\mathtt{loc}}   % Locations
\newcommand{\placeelem}{e}    % PlaceElems
\newcommand{\rustfield}{f}
\newcommand{\rustty}{T}
\newcommand{\maybelabelledregion}{\widetilde{r}}
\newcommand{\current}{\mathtt{current}}
\begin{array}{l l r}
    i && \textbf{(Integer)} \\
    \local && \textbf{(MIR Local)} \\
    c && \textbf{(MIR Constant)} \\
    b && \textbf{(MIR Basic Block Index)} \\
    l & ::= b[i] & \textbf{(MIR Location)} \\
    p && \textbf{(MIR Place)} \\
    \label & ::= & \textbf{(Label)} \\
    &\mid ~\texttt{start}~b &  \\
    &\mid ~\texttt{loop}~b &  \\
    &\mid ~\texttt{prepare}~l &  \\
    &\mid ~\texttt{before-collapse}~l &  \\
    &\mid ~\texttt{before-ref-assignment}~l &  \\
    &\mid ~\texttt{mid}~l &  \\
    &\mid ~\texttt{after}~l &  \\
    \maybelabelled & ::=  & \textbf{(Maybe-Labelled Place)} \\
    & \mid p & \text{(Current Place)} \\
    & \mid p~\mathtt{at}~\label & \text{(Labelled Place)} \\
    \pcgplace & ::=  & \textbf{(PCG Place)} \\
    & \mid \maybelabelled & \text{(Maybe-Labelled Place)} \\
    & \mid \remote{\local} & \text{(Remote Place)} \\
    \lifetimeproj & ::=  & \textbf{(Lifetime Projection)} \\
    & \mid \lproj{\pcgplace}{r} & \text{(Place Projection)} \\
    & \mid \lproj{\pcgplace}{r~\texttt{at}~\label} & \text{(Snapshot of Place Projection)} \\
    & \mid \lproj{\pcgplace}{r~\texttt{at}~\placeholderlabel} & \text{(Placeholder Projection)} \\
    & \mid \lproj{\const}{\lifetime} & \text{(Constant Projection)} \\
    n & ::= \pcgplace~|~\lifetimeproj & \textbf{(PCG Node)}
\end{array}
$$

<div class="warning">
We probably don't need so many label types, but we have them in the implementation currently.
</div>

<div class="warning">
In the implementation we currently refer to lifetime projections as "region projections" and labelled places as "old" places.
</div>

## Associated Place

The associated place of a PCG node $n$ is defined by the partial function $p(n)$ :
- $p(p) = p$
- $p(p~\texttt{at}~\label) = p$
- $p(\lifetimeproj) = p(\base(\lifetimeproj))$

Where $\base(\lifetimeproj)$ is the base of the lifetime projection $\lifetimeproj$ as defined [here](lifetime-projections.html#lifetime-projection-base).

## Local PCG Nodes

A PCG node $n$ is a local node if it has an associated place $p(n)$.
