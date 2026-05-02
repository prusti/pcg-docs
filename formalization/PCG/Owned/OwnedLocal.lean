import Core.Dsl.DefEnum
import PCG.Owned.InitTree

defEnum OwnedLocal
    (.text "ol", .text "OwnedLocal")
  "Owned Locals"
  (doc! "An owned local \
    {Doc.defMath (.text "ol") (.text "OwnedLocal")} is either \
    unallocated, or allocated and carrying an initialisation \
    tree describing the initialisation state of its \
    sub-places.")
where
  | unallocated
    "Unallocated."
  | allocated (it : InitTree)
    "Allocated."
  deriving Repr
