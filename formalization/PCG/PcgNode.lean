import Core.Dsl.DefEnum
import PCG.LifetimeProjection
import PCG.PcgPlace

defEnum PcgNode {P}
    (.doc (.plain "n"), .doc (.plain "PcgNode"))
  "PCG Nodes"
  (.plain "A PCG node is either a PCG place or a lifetime \
   projection whose base is a PCG place and whose index is \
   a natural number.")
where
  | place (p : PcgPlace P)
    "A PCG place node."
    (#p)
  | lifetimeProjection (lp : LifetimeProjection (PcgPlace P) Nat)
    "A lifetime projection node with a PCG place base and \
     natural-number index."
    (#lp)
