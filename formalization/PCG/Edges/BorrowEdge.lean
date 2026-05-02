import Core.Dsl.DefStruct
import MIR.Body
import MIR.Region
import MIR.Ty
import PCG.Nodes.LPLabel
import PCG.Nodes.MaybeLabelled

defStruct BorrowEdge {P}
    (.text "be", .text "BorrowEdge")
  "Borrow Edges"
  (doc! "A borrow edge \
    {.math (.seq [(.text "be"), .sym .setContains, (.text "BorrowEdge"), .sym .space, .raw "P"])} \
    records a borrow introduced by an `&`-expression: it \
    connects the `blocked` place (the place that is blocked \
    by the borrow — e.g. `y` in `let x = &mut y`) to the \
    `assignedRef` (the place the borrow is assigned to — \
    e.g. `x` in the same example). It also carries the \
    mutability of the borrow, the MIR location at which it \
    was reserved, the region (lifetime) of the resulting \
    reference, and an optional label for the lifetime \
    projection of the assigned reference.")
where
  | blocked (doc! "The place that is blocked by the borrow (e.g. `y` in `let x = &mut y`).")
      : MaybeLabelled P
  | assignedRef (doc! "The place that is assigned by the borrow (e.g. `x` in `let x = &mut y`).")
      : MaybeLabelled P
  | kind "Mutability of the borrow." : Mutability
  | reserveLocation "The MIR location at which the borrow \
      was created." : Location
  | region "The region (lifetime) of the resulting \
      reference." : Region
  | assignedLPLabel "Optional label for the lifetime \
      projection of the assigned reference."
      : Option LPLabel
  deriving BEq, Repr, Hashable
