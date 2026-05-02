import Core.Dsl.DefStruct
import PCG.Nodes.LocalLifetimeProjection
import PCG.Nodes.PcgLifetimeProjection

defStruct BorrowFlowEdge {P}
    (.text "bfe",
     .text "BorrowFlowEdge")
  "Borrow-Flow Edges"
  (doc! "A borrow-flow edge \
    $_bfe_ ∈ _BorrowFlowEdge_$ \
    represents the flow of borrows between a source PCG \
    lifetime projection and a target local lifetime \
    projection over the place set $#P$.")
where
  | source "Source projection." : PcgLifetimeProjection P
  | target "Target projection." : LocalLifetimeProjection P
  deriving BEq, Repr, Hashable
