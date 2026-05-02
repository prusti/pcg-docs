import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.MaybeLabelled

defAlias LocalLifetimeProjection {P}
    (.text "llp",
     .text "LocalLifetimeProjection")
  "Local Lifetime Projections"
  (.seq [
    .plain "A local lifetime projection ",
    .math (.seq [.text "llp", .sym .setContains, .text "LocalLifetimeProjection", .sym .space, .raw "P"]),
    .plain " is a lifetime projection whose base is a \
     maybe-labelled place drawn from the parameter set ",
    .math (.text "P"),
    .plain " and whose index is a natural number."])
  := LifetimeProjection (MaybeLabelled P) Nat
