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
\newcommand{\maybelabelled}{\widetilde{p}}
\newcommand{\maybelabelledregion}{\widetilde{r}}
\newcommand{\current}{\mathtt{current}}
\newcommand{\pcgplace}{\hat{p}}
\newcommand{\remote}[1]{\mathit{remote}(#1)}
\newcommand{\lifetimeproj}{\mathit{rp}}
\newcommand{\lproj}[2]{#1 \downarrow #2}
\newcommand{\const}{\mathtt{const}}
\newcommand{\placeholderlabel}{\texttt{FUTURE}}
\newcommand{\label}{\ell}
\newcommand{\lifetime}{r}
\begin{array}{l l r}
    i && \textbf{(Integer)} \\
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
    \maybelabelledregion & ::=  & \textbf{(Maybe-Labelled Lifetime)} \\
    & \mid r & \text{(Current Lifetime)} \\
    & \mid r~\mathtt{at}~\label & \text{(Snapshotted Lifetime)} \\
    & \mid r~\mathtt{at}~\placeholderlabel & \text{(Placeholder Lifetime)} \\
    \pcgplace & ::=  & \textbf{(PCG Place)} \\
    & \mid \maybelabelled & \text{(Maybe-Labelled Place)} \\
    & \mid \remote{i} & \text{(Remote Place)} \\
    \lifetimeproj & ::=  & \textbf{(Lifetime Projection)} \\
    & \mid \lproj{\pcgplace}{\maybelabelledregion} & \text{(Place Projection)} \\
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
