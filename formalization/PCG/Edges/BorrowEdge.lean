import Core.Dsl.DefStruct
import MIR.Body
import MIR.Region
import MIR.Ty
import PCG.Nodes.LifetimeProjectionLabel
import PCG.Nodes.MaybeLabelled

defStruct BorrowEdge {P}
    (.text "be", .text "BorrowEdge")
  "Borrow Edges"
  (.seq [
    .plain "A borrow edge ",
    Doc.defMath (.text "be")
      (.text "BorrowEdge") ["P"],
    .plain " records a borrow introduced by an ",
    .code "&",
    .plain "-expression: it connects the ",
    .code "blocked", .plain " place (the place that is \
     blocked by the borrow — e.g. ",
    .code "y", .plain " in ", .code "let x = &mut y",
    .plain ") to the ", .code "assignedRef",
    .plain " (the place the borrow is assigned to — e.g. ",
    .code "x", .plain " in the same example). It also \
     carries the mutability of the borrow, the MIR location \
     at which it was reserved, the region (lifetime) of the \
     resulting reference, and an optional label for the \
     lifetime projection of the assigned reference."])
where
  | blocked (.seq [
        .plain "The place that is blocked by the borrow \
          (e.g. ",
        .code "y", .plain " in ", .code "let x = &mut y",
        .plain ")."])
      : MaybeLabelled P
  | assignedRef (.seq [
        .plain "The place that is assigned by the borrow \
          (e.g. ",
        .code "x", .plain " in ", .code "let x = &mut y",
        .plain ")."])
      : MaybeLabelled P
  | kind "Mutability of the borrow." : Mutability
  | reserveLocation "The MIR location at which the borrow \
      was created." : Location
  | region "The region (lifetime) of the resulting \
      reference." : Region
  | assignedLPLabel "Optional label for the lifetime \
      projection of the assigned reference."
      : Option LifetimeProjectionLabel
  deriving BEq, Repr, Hashable
