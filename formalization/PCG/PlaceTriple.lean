import Core.Dsl.DefStruct
import MIR.Place
import PCG.Capability

defStruct PlaceTriple
    (.doc (.plain "pt"), .doc (.plain "PlaceTriple"))
  "Place Triples"
  (.seq [
    .plain "A place triple ",
    Doc.defMath (.doc (.plain "pt"))
      (.doc (.plain "PlaceTriple")),
    .plain " bundles a place with the capability required for \
     the place before a statement executes and the optional \
     capability established for the place after the statement \
     executes. A ", .code "None",
    .plain " post indicates that the statement does not \
     establish a post-condition capability on the place."])
where
  | place "The place whose capability is tracked." : Place
  | pre "The capability required on the place before the \
      statement." : Capability
  | post "The capability established on the place after the \
      statement, when one is established."
      : Option Capability
  deriving BEq, Repr, Hashable
