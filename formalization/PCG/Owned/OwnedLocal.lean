import Core.Dsl.DefEnum
import PCG.Owned.InitialisationTree

defEnum OwnedLocal
    (.doc (.plain "ol"), .doc (.plain "OwnedLocal"))
  "Owned Locals"
  (.seq [
    .plain "An owned local ",
    Doc.defMath (.doc (.plain "ol"))
      (.doc (.plain "OwnedLocal")),
    .plain " is either unallocated, or allocated and carrying \
     an initialisation tree describing the initialisation \
     state of its sub-places."])
where
  | unallocated
    "Unallocated."
    (.bold (.raw "U"))
  | allocated (it : InitialisationTree)
    "Allocated."
  deriving Repr
