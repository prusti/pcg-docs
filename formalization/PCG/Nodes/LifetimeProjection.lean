import Core.Dsl.DefStruct
import PCG.Nodes.LPLabel

defStruct LifetimeProjection {B I}
    (.text "lp", .text "LifetimeProjection")
  "Lifetime Projections"
  (.seq [
    .plain "A lifetime projection ",
    .math (.seq [.text "lp", .sym .setContains, .text "LifetimeProjection", .sym .space, .raw "B", .sym .space, .raw "I"]),
    .plain " consists of a base drawn from a parameter set ",
    .math (.text "B"),
    .plain ", an index drawn from a parameter set ",
    .math (.text "I"),
    .plain ", and an optional label identifying the \
     snapshot location (or ",
    .math (.doc (.code "FUTURE")),
    .plain " placeholder) at which the projection is taken."])
where
  | base "Base of the projection." : B
  | index "Index of the projection." : I
  | label "Optional lifetime projection label."
      : Option LPLabel
  deriving DecidableEq, BEq, Repr, Hashable
