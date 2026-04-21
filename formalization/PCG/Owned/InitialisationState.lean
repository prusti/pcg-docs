import Core.Dsl.DefEnum

defEnum InitialisationState (.raw "i", .raw "I")
  "Initialisation States"
  (.seq [
    .plain "An initialisation state ",
    Doc.defMath (.raw "i") (.raw "I"),
    .plain " describes whether an owned place is \
     uninitialised (",
    .math (.bold (.raw "U")),
    .plain "), shallowly initialised (",
    .math (.bold (.raw "S")),
    .plain "), or fully initialised (",
    .math (.bold (.raw "D")),
    .plain ") at a particular program point. Each leaf node \
     in the initialisation state tree carries one of these \
     values."])
where
  | uninit
    "Uninitialised or moved-out (no reads are permitted; \
     only writes, to re-initialise the place, are allowed)."
    (.bold (.raw "U"))
  | shallow
    "Shallowly initialised (the place itself holds a valid \
     value, but memory behind a dereference may not be \
     initialised; arises only for `Box`-typed places)."
    (.bold (.raw "S"))
  | deep
    "Fully initialised (all memory reachable from this \
     place, including through dereferences, is valid and \
     accessible)."
    (.bold (.raw "D"))
