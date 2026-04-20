import Core.Dsl.DefEnum
import PCG.Nodes.PcgLifetimeProjection
import PCG.Nodes.PcgPlace

defEnum PcgNode {P}
    (.doc (.plain "n"), .doc (.plain "PcgNode"))
  "PCG Nodes"
  (.seq [
    .plain "A PCG node ",
    Doc.defMath (.doc (.plain "n"))
      (.doc (.plain "PcgNode")) ["P"],
    .plain " is either a PCG place or a PCG lifetime \
     projection."])
where
  | place (p : PcgPlace P)
    "A PCG place."
    (#p)
  | lifetimeProjection (lp : PcgLifetimeProjection P)
    "A PCG lifetime projection."
    (#lp)
  deriving BEq, Repr, Hashable
