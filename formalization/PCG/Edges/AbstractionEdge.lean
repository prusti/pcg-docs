import Core.Dsl.DefEnum
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.PcgNode
import PCG.Nodes.PcgPlace

defEnum AbstractionEdge {P}
    (.text "a", .text "AbstractionEdge")
  "Abstraction Edges"
  (doc! "An abstraction edge \
    $_a_ ∈ _AbstractionEdge_$ \
    represents the flow of borrows introduced due to a \
    function call or a loop. A function call abstraction \
    edge connects a source lifetime projection to a target \
    lifetime projection. A loop abstraction edge connects a \
    source lifetime projection to a target PCG node.")
where
  | fnCall (source : LifetimeProjection (PcgPlace P) Nat)
      (target : LifetimeProjection (PcgPlace P) Nat)
    "A function call abstraction edge."
    (mathdoc! "{source}→{target}")
  | loop (source : LifetimeProjection (PcgPlace P) Nat)
      (target : PcgNode P)
    "A loop abstraction edge."
    (mathdoc! "{source}→{target}")
  deriving BEq, Repr, Hashable
