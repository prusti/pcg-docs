import Core.Dsl.DefAlias
import PCG.Owned.AbstractInitTree
import PCG.Owned.InitialisationState

defAlias InitialisationTree
    (.doc (.plain "it"),
     .doc (.plain "InitialisationTree"))
  "Initialisation Trees"
  (.seq [
    .plain "An initialisation tree ",
    Doc.defMath (.doc (.plain "it"))
      (.doc (.plain "InitialisationTree")),
    .plain " describes the initialisation state of an owned \
     place: an abstract initialisation tree whose leaves each \
     carry an initialisation state. By invariant, an internal \
     node has at least one descendant leaf that is not fully \
     initialised (otherwise the subtree collapses to a single ",
    .math (.bold (.raw "D")),
    .plain " leaf)."])
  := AbstractInitTree InitialisationState
