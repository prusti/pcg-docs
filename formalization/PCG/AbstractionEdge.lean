import Core.Dsl.DefEnum
import PCG.LifetimeProjection
import PCG.PcgNode
import PCG.PcgPlace

defEnum AbstractionEdge {P}
    (.doc (.plain "a"), .doc (.plain "AbstractionEdge"))
  "Abstraction Edges"
  (.seq [
    .plain "An abstraction edge ",
    Doc.defMath (.doc (.plain "a"))
      (.doc (.plain "AbstractionEdge")),
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
    (#source, .doc (.plain " → "), #target)
  | loop (source : LifetimeProjection (PcgPlace P) Nat)
      (target : PcgNode P)
    "A loop abstraction edge."
    (#source, .doc (.plain " → "), #target)
