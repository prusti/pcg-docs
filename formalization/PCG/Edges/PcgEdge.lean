import Core.Dsl.DefEnum
import PCG.Edges.AbstractionEdge
import PCG.Edges.BorrowFlowEdge
import PCG.Edges.DerefEdge
import PCG.Edges.UnpackEdge
import PCG.Nodes.PcgNode

defEnum PcgEdge {P}
    (.doc (.plain "e"), .doc (.plain "PcgEdge"))
  "PCG Edges"
  (.seq [
    .plain "A PCG edge ",
    Doc.defMath (.doc (.plain "e"))
      (.doc (.plain "PcgEdge")) ["P"],
    .plain " is one of the four edge kinds that may appear in \
     a PCG hypergraph: an unpack edge on owned nodes, a deref \
     edge through a reference or box, a borrow-flow edge \
     between lifetime projections, or an abstraction edge \
     introduced by a function call or loop."])
where
  | unpack (e : UnpackEdge (PcgNode P))
    "An unpack edge over PCG nodes."
    (#e)
  | deref (e : DerefEdge P)
    "A deref edge."
    (#e)
  | borrowFlow (e : BorrowFlowEdge P)
    "A borrow-flow edge."
    (#e)
  | abstraction (e : AbstractionEdge P)
    "An abstraction edge."
    (#e)
  deriving BEq, Repr, Hashable
