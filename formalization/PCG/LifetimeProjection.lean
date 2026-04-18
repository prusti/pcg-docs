import Core.Dsl.DefStruct

defStruct LifetimeProjection {B I}
    (.doc (.plain "lp"), .doc (.plain "LifetimeProjection"))
  "Lifetime Projections"
  "A lifetime projection: a pair of a base drawn from a \
   set B and an index drawn from a set I. The base and \
   index sets are parameters of the definition."
where
  | base "The base of the projection (drawn from set B)."
      : B
  | index "The index of the projection (drawn from set I)."
      : I
