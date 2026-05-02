import Core.Dsl.DefAlias
import PCG.Owned.AbstractInitTree
import PCG.Owned.MaterializedTreeLeaf

defAlias MaterializedTree
    (.text "mt",
     .text "MaterializedTree")
  "Materialised Trees"
  (doc! "A materialised tree \
    {.math (.seq [(.text "mt"), .sym .setContains, (.text "MaterializedTree")])} \
    is an abstract initialisation tree whose leaves are \
    materialised-tree leaves: either uninitialised, shallowly \
    initialised, or fully initialised together with an \
    optional materialised extension growing off the leaf to \
    reach sub-places that are targets of borrows in the \
    borrow PCG.")
  := AbstractInitTree MaterializedTreeLeaf
