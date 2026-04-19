import Core.Dsl.DefEnum

defEnum InitialisationState (.raw "i", .raw "I")
  "Initialisation States"
  (.plain "An initialisation state describes whether an owned \
   place is initialised, shallowly initialised, or uninitialised \
   at a particular program point. Each leaf node in the \
   initialisation state tree carries one of these values.")
where
  | uninit
    "Uninitialised or moved-out. No reads are permitted; only \
     writes (to re-initialise the place) are allowed."
    (.bold (.raw "U"))
  | shallow
    "Shallowly initialised: the place itself holds a valid \
     value, but memory behind a dereference may not be \
     initialised. Arises only for `Box`-typed places."
    (.bold (.raw "S"))
  | deep
    "Fully initialised. All memory reachable from this place \
     (including through dereferences) is valid and accessible."
    (.bold (.raw "D"))
