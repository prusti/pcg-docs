import OpSem.Machine
import OpSem.RuntimePlace
import Core.Dsl.Descr

namespace Machine

descr (.seq [
  .plain "Based on statements as described ",
  .link (.plain "here")
    "https://github.com/minirust/minirust/\
     blob/master/spec/lang/step/statements.md"])

defFn placeStore (.plain "placeStore")
  (.seq [.plain "Store a value into the location \
    designated by a runtime place. Alignment and \
    atomicity are not currently modelled, so this \
    simply delegates to ",
    .code "typedStore",
    .plain " using the place's thin pointer."])
  (m "The memory." : Memory)
  (place "The place to store into." : RuntimePlace)
  (v "The value to store." : Value)
  : Memory :=
    typedStore ‹m, place↦ptr, v›

defFn placeLoad (.plain "placeLoad")
  (.seq [.plain "Load a value from the location \
    designated by a runtime place. Alignment and \
    atomicity are not currently modelled, so this \
    simply delegates to ",
    .code "typedLoad",
    .plain " using the place's thin pointer."])
  (m "The memory." : Memory)
  (place "The place to load from." : RuntimePlace)
  (ty "The type to load." : Ty)
  : Option Value :=
    typedLoad ‹m, place↦ptr, ty›

end Machine
