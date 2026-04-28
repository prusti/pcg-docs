import Core.Dsl.DefEnum
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.PcgNode
import PCG.Nodes.PcgPlace

defEnum AbstractionEdge {P}
    (.text "a", .text "AbstractionEdge")
  "Abstraction Edges"
  (.seq [
    .plain "An abstraction edge ",
    Doc.defMath (.text "a")
      (.text "AbstractionEdge"),
    .plain " represents the flow of borrows introduced due \
     to a function call or a loop. A function call \
     abstraction edge connects a source lifetime projection \
     to a target lifetime projection. A loop abstraction \
     edge connects a source lifetime projection to a target \
     PCG node."])
where
  | fnCall (source : LifetimeProjection (PcgPlace P) Nat)
      (target : LifetimeProjection (PcgPlace P) Nat)
    "A function call abstraction edge."
    (#source, .text " → ", #target)
  | loop (source : LifetimeProjection (PcgPlace P) Nat)
      (target : PcgNode P)
    "A loop abstraction edge."
    (#source, .text " → ", #target)
  deriving BEq, Repr, Hashable
