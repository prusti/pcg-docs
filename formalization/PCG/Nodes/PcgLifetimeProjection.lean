import Core.Dsl.DefAlias
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.PcgLifetimeProjectionBase

defAlias PcgLifetimeProjection {P}
    (.doc (.plain "plp"),
     .doc (.plain "PcgLifetimeProjection"))
  "PCG Lifetime Projections"
  (.seq [
    .plain "A PCG lifetime projection ",
    Doc.defMath (.doc (.plain "plp"))
      (.doc (.plain "PcgLifetimeProjection")) ["P"],
    .plain " is a lifetime projection whose base is a PCG \
     lifetime projection base over the parameter set ",
    .math (.doc (.plain "P")),
    .plain " and whose index is a natural number."])
  := LifetimeProjection (PcgLifetimeProjectionBase P) Nat
