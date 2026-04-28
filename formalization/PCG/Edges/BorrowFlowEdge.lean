import Core.Dsl.DefStruct
import PCG.Nodes.LocalLifetimeProjection
import PCG.Nodes.PcgLifetimeProjection

defStruct BorrowFlowEdge {P}
    (.text "bfe",
     .text "BorrowFlowEdge")
  "Borrow-Flow Edges"
  (.seq [
    .plain "A borrow-flow edge ",
    Doc.defMath (.text "bfe")
      (.text "BorrowFlowEdge"),
    .plain " represents the flow of borrows between a source \
     PCG lifetime projection and a target local lifetime \
     projection over the place set ",
    .math (.text "P"),
    .plain "."])
where
  | source "Source projection." : PcgLifetimeProjection P
  | target "Target projection." : LocalLifetimeProjection P
  deriving BEq, Repr, Hashable
