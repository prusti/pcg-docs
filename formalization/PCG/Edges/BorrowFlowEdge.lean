import Core.Dsl.DefStruct
import PCG.Nodes.LocalLifetimeProjection
import PCG.Nodes.PcgLifetimeProjection

defStruct BorrowFlowEdge {P}
    (.doc (.plain "bfe"),
     .doc (.plain "BorrowFlowEdge"))
  "Borrow-Flow Edges"
  (.seq [
    .plain "A borrow-flow edge ",
    Doc.defMath (.doc (.plain "bfe"))
      (.doc (.plain "BorrowFlowEdge")),
    .plain " represents the flow of borrows between a source \
     PCG lifetime projection and a target local lifetime \
     projection over the place set ",
    .math (.doc (.plain "P")),
    .plain "."])
where
  | source "Source projection." : PcgLifetimeProjection P
  | target "Target projection." : LocalLifetimeProjection P
  deriving BEq, Repr, Hashable
