import Core.Dsl.DefStruct
import PCG.Edges.PcgEdge
import PCG.ValidityConditions

defStruct BorrowsGraph {P}
    (.doc (.plain "bg"),
     .doc (.plain "BorrowsGraph"))
  "Borrows Graphs"
  (.seq [
    .plain "A borrows graph ",
    Doc.defMath (.doc (.plain "bg"))
      (.doc (.plain "BorrowsGraph")) ["P"],
    .plain " is the portion of the PCG that tracks borrow \
     edges: it maps each PCG edge to the validity conditions \
     under which the edge holds."]) subscript
where
  | edges "Map from each edge in the graph to the validity \
       conditions under which it holds."
      : Map (PcgEdge P) ValidityConditions
  deriving Repr
