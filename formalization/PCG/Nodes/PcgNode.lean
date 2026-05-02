import Core.Dsl.DefEnum
import PCG.Nodes.PcgLifetimeProjection
import PCG.Nodes.PcgPlace

defEnum PcgNode {P}
    (.text "n", .text "PcgNode")
  "PCG Nodes"
  (doc! "A PCG node \
    $_n_ ∈ _PcgNode_ _P_$ \
    is either a PCG place or a PCG lifetime projection.")
where
  | place (p : PcgPlace P)
    "A PCG place."
    (#p)
  | lifetimeProjection (lp : PcgLifetimeProjection P)
    "A PCG lifetime projection."
    (#lp)
  deriving BEq, Repr, Hashable
