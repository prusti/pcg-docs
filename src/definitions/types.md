# Types

A _type_ $\defn{ty}{\ty}$ is either:
- A type parameter of the form $\text{param}~i$
- An alias type of the form $\ty::T\langle\overline{\ty}\rangle$
- A _type constructor application_ of the form $T\langle\overline{\ty}\rangle$
- A box type of the form $\text{Box}\langle\ty\rangle$

## Corresponding Regions

If $r$ is a region in $\ty$, the _corresponding region_ $r_c$ in a type $\ty_c$ is:

If $\ty = \texttt{\&}~r~m~\ty'$ and $\ty_c = \texttt{\&}~r_c'~m~\ty_c'$ then $r_c = r_c'$

If $\ty = T\langle\ty_1, \ldots, t_n\rangle$  and $\ty_c =
T\langle\ty_{c_1}, \ldots, t_{c_n}\rangle$, iterate $i$ over $1, \ldots, n$,
and if there exists an $r_c'$ where $r_c'$ in $\ty_{c_i}$ is the corresponding
region of $r$ in $t_i$, then $r_c = r_c'$.
