# Lifetime Projections

Lifetime projections take the following form

$$
\begin{array}{l l r}
\lifetimeproj & ::=  & \textbf{(Lifetime Projection)} \\
& \mid \lproj{\pcgplace}{r} & \text{(Place Projection)} \\
& \mid \lproj{\pcgplace}{r~\texttt{at}~\label} & \text{(Snapshot of Place Projection)} \\
& \mid \lproj{\pcgplace}{r~\texttt{at}~\placeholderlabel} & \text{(Placeholder Projection)} \\
& \mid \lproj{\const}{\lifetime} & \text{(Constant Projection)}
\end{array}
$$

## Lifetime Projection Lifetime

The *lifetime* $\lifetime(\lifetimeproj)$ of a lifetime projection
$\lifetimeproj$ is conceptually the lifetime $r$ on the right of the $\downarrow$, i.e:
- $\lifetime(\lproj{\pcgplace}{r}) = r$
- $\lifetime(\lproj{\pcgplace}{r}~\texttt{at}~\label) = r$
- $\lifetime(\lproj{\pcgplace}{r}~\texttt{at}~\placeholderlabel) = r$
- $\lifetime(\lproj{\const}{r}) = r$

## Lifetime Projection Base

The *base* $\base(\lifetimeproj)$ of a lifetime projection $\lifetimeproj$ is
conceptually the part on the left of the $\downarrow$, i.e. defined as follows:
- $\base(\lproj{\pcgplace}{r}) = \pcgplace$
- $\base(\lproj{\pcgplace}{r}~\texttt{at}~\label) = \pcgplace$
- $\base(\lproj{\pcgplace}{r}~\texttt{at}~\placeholderlabel) = \pcgplace$
- $\base(\lproj{\const}{r}) = \const$
