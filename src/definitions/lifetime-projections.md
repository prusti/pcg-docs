# Lifetime Projections

## Generalized Lifetimes

A _generalized lifetime_ $\defn{glft}{\glft}$ is either a region $r$ or $\defn{regionsin}{\regionsin{\ty}}$, where
$\ty$ is either:
1. a type parameter, or
2. a type alias that cannot be normalized

## Generalized Lifetime Projections

A _generalized lifetime projection_ $\defn{glproj}{\glproj}$ takes the form
$\defn{lproj}{\lproj{b}{\glft}}$ where $b$ is a _base_ having an associated type
$\ty$.
The _index_ $\defn{lpindex}{\lpindex{\glproj}}$ of a lifetime projection
is the index of the occurence of $\glft$ in the _generalized lifetime list_
$\defn{glfts}{\glfts(\ty)}$ (the list of generalized lifetimes in $\ty$,
occurring in the order they appear in $\ty$, and with duplicates removed).

A _lifetime projection_ is a generalized lifetime projection of the form
$\lproj{b}{r}$ (that is, a generalized lifetime projection where the associated
generalized lifetime is a region).

## PCG Lifetime Projections

PCG lifetime projections take the following form

$$
\begin{array}{l l r}
\defn{lifetimeproj}{\lifetimeproj} & ::=  & \textbf{(Lifetime Projection)} \\
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
