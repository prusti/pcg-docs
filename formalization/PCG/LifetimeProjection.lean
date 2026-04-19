import Core.Dsl.DefStruct
import PCG.LifetimeProjectionLabel

defStruct LifetimeProjection {B I}
    (.doc (.plain "lp"), .doc (.plain "LifetimeProjection"))
  "Lifetime Projections"
  (.plain "A lifetime projection: a base drawn from a set B, \
   an index drawn from a set I, and an optional lifetime \
   projection label identifying the snapshot location or \
   FUTURE placeholder at which the projection is taken. The \
   base and index sets are parameters of the definition.")
where
  | base "The base of the projection (drawn from set B)."
      : B
  | index "The index of the projection (drawn from set I)."
      : I
  | label "The optional lifetime projection label."
      : Option LifetimeProjectionLabel
