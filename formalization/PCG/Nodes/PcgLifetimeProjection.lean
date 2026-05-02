import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.PcgLifetimeProjectionBase

defAlias PcgLifetimeProjection {P}
    (.text "plp",
     .text "PcgLifetimeProjection")
  "PCG Lifetime Projections"
  (doc! "A PCG lifetime projection \
    $_plp_ ∈ _PcgLifetimeProjection_ _P_$ \
    is a lifetime projection whose base is a PCG lifetime \
    projection base over the parameter set $#P$ and whose \
    index is a natural number.")
  := LifetimeProjection (PcgLifetimeProjectionBase P) Nat
