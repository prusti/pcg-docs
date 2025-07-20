# Choosing Place Labels


When the PCG analysis labels a place, all references to the *current version* of
the place (i.e. not within already labelled places) are labelled with a label
corresponding to the last time the place could have been updated.

To accomplish this, the PCG uses a data structure called the *Latest Map* to
track, for each place, the most recent location where it could have been updated.

<div class="warning">

We could consider instead to label locations at the point it is required (as is
done when labelling lifetime projection). Our current approach involves a lot of
bookkeeping.

</div>


## The *Latest Map*

The *Latest Map* $\mathcal{L}$ is a partial map from places to labels.

The function $\mathit{latest}(p)$ is defined as follows:

$$
\mathit{latest}(p) = \begin{cases}
\mathcal{L}[p']& \text{if there exists a}~p'\in\mathcal{L}~\text{where}~p'~\text{is a prefix or a postfix of}~p \\
\mathtt{start~bb0}&\text{otherwise}
\end{cases}
$$

We note that for each place $p$, either $\mathcal{L}$ does not contain any place
that is either a prefix or postfix of $p$, or it contains exactly one such
place. This is ensured by construction.
