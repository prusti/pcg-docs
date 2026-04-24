import Core.Dsl.DefStruct
import MIR.Body

defStruct Program (.doc (.plain "prog"),
    .doc (.plain "Program"))
  "Programs"
  (.seq [
    .plain "A program ",
    Doc.defMath (.doc (.plain "prog"))
      (.doc (.plain "Program")),
    .plain " bundles every function known to the PCG together \
     with the name of the entry point. Each function is keyed \
     by its name so calls can be resolved by looking the \
     callee's name up in the map."])
where
  | functions "The function bodies keyed by function name."
      : Map String Body
  | start "The name of the entry function." : String
  deriving Repr
