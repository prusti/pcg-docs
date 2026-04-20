import Core.Dsl.DefEnum
import PCG.LifetimeProjection
import PCG.PcgPlace

defEnum PcgNode {P}
    (.doc (.plain "n"), .doc (.plain "PcgNode"))
  "PCG Nodes"
  (.seq [
    .plain "A PCG node ",
    Doc.defMath (.doc (.plain "n"))
      (.doc (.plain "PcgNode")) ["P"],
    .plain " is either a PCG place or a lifetime projection \
     (whose base is a PCG place and whose index is a natural \
     number)."])
where
  | place (p : PcgPlace P)
    "A PCG place."
    (#p)
  | lifetimeProjection (lp : LifetimeProjection (PcgPlace P) Nat)
    "A lifetime projection."
    (#lp)
