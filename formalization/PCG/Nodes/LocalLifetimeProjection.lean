import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.MaybeLabelled

defAlias LocalLifetimeProjection {P}
    (.doc (.plain "llp"),
     .doc (.plain "LocalLifetimeProjection"))
  "Local Lifetime Projections"
  (.seq [
    .plain "A local lifetime projection ",
    Doc.defMath (.doc (.plain "llp"))
      (.doc (.plain "LocalLifetimeProjection")) ["P"],
    .plain " is a lifetime projection whose base is a \
     maybe-labelled place drawn from the parameter set ",
    .math (.doc (.plain "P")),
    .plain " and whose index is a natural number."])
  := LifetimeProjection (MaybeLabelled P) Nat
