import Core.Dsl.DefFn
import Core.Dsl.DefStruct
import MIR.Place
import PCG.Edges.PcgEdge
import PCG.ValidityConditions

defStruct BorrowsGraph {P}
    (.text "bg",
     .text "BorrowsGraph")
  "Borrows Graphs"
  (doc! "A borrows graph \
    {.math (.seq [(.text "bg"), .sym .setContains, (.text "BorrowsGraph"), .sym .space, .raw "P"])} \
    is the portion of the PCG that tracks borrow edges: it \
    maps each PCG edge to the validity conditions under \
    which the edge holds.") subscript
where
  | edges "Map from each edge in the graph to the validity \
       conditions under which it holds."
      : Map (PcgEdge P) ValidityConditions
  deriving Repr

namespace BorrowsGraph

defFn join (.plain "join")
  (doc! "Join two borrows graphs by merging their edge maps. \
    An edge present in only one graph is kept with its \
    validity conditions unchanged; for edges present in both \
    graphs the validity conditions are combined with \
    `ValidityConditions.join` (pointwise \
    {Doc.math (.sym .cup)} of the allowed-target sets per \
    source block).")
  (bg1 "First borrows graph." : BorrowsGraph Place)
  (bg2 "Second borrows graph." : BorrowsGraph Place)
  : BorrowsGraph Place :=
    BorrowsGraph⟨mapMergeWith ‹ValidityConditions.join,
      bg1↦edges, bg2↦edges›⟩

end BorrowsGraph
