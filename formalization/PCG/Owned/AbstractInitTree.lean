import Core.Dsl.DefEnum
import PCG.PlaceExpansion

defEnum AbstractInitTree {D}
    (.text "t",
     .text "AbstractInitTree")
  "Abstract Initialisation Trees"
  (doc! "An abstract initialisation tree \
    {.math (.seq [(.text "t"), .sym .setContains, (.text "AbstractInitTree"), .sym .space, .raw "D"])} \
    is either a leaf carrying a value drawn from the \
    parameter set $#D$, or an internal (unpacked) node \
    whose place expansion stores each child's sub-tree as \
    the per-child payload. The leaf-data type is a parameter \
    so that the ordinary initialisation tree and \
    materialised tree share a single recursive structure.") long
where
  | leaf (d : D)
    "A leaf carrying a per-place payload."
  | internal (expansion : PlaceExpansion (AbstractInitTree D))
    "An internal (unpacked) node."
  deriving Repr
