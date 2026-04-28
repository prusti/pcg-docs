import Core.Dsl.DefEnum
import PCG.Owned.InitTree

defEnum OwnedLocal
    (.text "ol", .text "OwnedLocal")
  "Owned Locals"
  (.seq [
    .plain "An owned local ",
    Doc.defMath (.text "ol")
      (.text "OwnedLocal"),
    .plain " is either unallocated, or allocated and carrying \
     an initialisation tree describing the initialisation \
     state of its sub-places."])
where
  | unallocated
    "Unallocated."
    (.bold (.raw "U"))
  | allocated (it : InitTree)
    "Allocated."
  deriving Repr
