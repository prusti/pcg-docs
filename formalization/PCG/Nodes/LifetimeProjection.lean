import Core.Dsl.DefStruct
import PCG.Nodes.LPLabel

defStruct LifetimeProjection {B I}
    (.text "lp", .text "LifetimeProjection")
  "Lifetime Projections"
  (doc! "A lifetime projection \
    $_lp_ ∈ _LifetimeProjection_ _B_ _I_$ \
    consists of a base drawn from a parameter set $#B$, \
    an index drawn from a parameter set $#I$, and an optional \
    label identifying the snapshot location (or \
    {Doc.math (.doc (.code "FUTURE"))} placeholder) at which \
    the projection is taken.")
where
  | base "Base of the projection." : B
  | index "Index of the projection." : I
  | label "Optional lifetime projection label."
      : Option LPLabel
  deriving DecidableEq, BEq, Repr, Hashable
