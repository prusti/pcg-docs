import OpSem.Machine
import OpSem.RuntimePlace

namespace Machine

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

end Machine
