import Core.Dsl.DefEnum
import PCG.Owned.InitialisationState
import PCG.PlaceExpansion

defEnum InitialisationTree
    (.doc (.plain "it"),
     .doc (.plain "InitialisationTree"))
  "Initialisation Trees"
  (.seq [
    .plain "An initialisation tree ",
    Doc.defMath (.doc (.plain "it"))
      (.doc (.plain "InitialisationTree")),
    .plain " describes the initialisation state of an owned \
     place: either a leaf carrying an initialisation \
     capability, or an internal (unpacked) node whose place \
     expansion stores each child's sub-tree as the per-child \
     payload. By invariant, an internal node has at least \
     one descendant leaf that is not fully initialised \
     (otherwise the subtree collapses to a single ",
    .math (.bold (.raw "D")),
    .plain " leaf)."])
where
  | leaf (cap : InitialisationState)
    "A leaf carrying an initialisation capability."
  | internal (expansion : PlaceExpansion InitialisationTree)
    "An internal (unpacked) node."
  deriving Repr
