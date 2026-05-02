import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.MaybeLabelled

defAlias LocalLifetimeProjection {P}
    (.text "llp",
     .text "LocalLifetimeProjection")
  "Local Lifetime Projections"
  (doc! "A local lifetime projection \
    $_llp_ ∈ _LocalLifetimeProjection_ _P_$ \
    is a lifetime projection whose base is a maybe-labelled \
    place drawn from the parameter set $#P$ and whose index \
    is a natural number.")
  := LifetimeProjection (MaybeLabelled P) Nat
