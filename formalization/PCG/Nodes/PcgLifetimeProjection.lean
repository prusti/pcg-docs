import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.PcgLifetimeProjectionBase

defAlias PcgLifetimeProjection {P}
    (.text "plp",
     .text "PcgLifetimeProjection")
  "PCG Lifetime Projections"
  (.seq [
    .plain "A PCG lifetime projection ",
    .math (.seq [.text "plp", .sym .setContains, .text "PcgLifetimeProjection", .sym .space, .raw "P"]),
    .plain " is a lifetime projection whose base is a PCG \
     lifetime projection base over the parameter set ",
    .math (.text "P"),
    .plain " and whose index is a natural number."])
  := LifetimeProjection (PcgLifetimeProjectionBase P) Nat
