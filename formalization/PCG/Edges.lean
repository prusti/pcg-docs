import Core.Dsl.Descr
import PCG.Edges.AbstractionEdge
import PCG.Edges.BorrowFlowEdge
import PCG.Edges.DerefEdge
import PCG.Edges.PcgEdge
import PCG.Edges.UnpackEdge

descr (.plain "PCG hyperedges: unpack edges on owned places, \
   deref edges through references and boxes, borrow-flow edges \
   between lifetime projections, and abstraction edges \
   introduced by function calls and loops.")
