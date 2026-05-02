import Core.Dsl.DefEnum

defEnum Capability (.raw "c", .raw "C")
  "Capabilities"
  (doc! "A capability $_c_ ∈ _C_$ \
    describes the actions permitted on a place at a particular \
    program point: either no capability (∅), \
    exclusive ($__E__$), read ($__R__$), write ($__W__$), or \
    shallow exclusive ($__e__$).")
where
  | none
    "No capability."
    (.sym .emptySet)
  | exclusive
    "Exclusive access."
    (.bold (.raw "E"))
  | read
    "Read access."
    (.bold (.raw "R"))
  | write
    "Write access."
    (.bold (.raw "W"))
  | shallowExclusive
    "Shallow exclusive access."
    (.bold (.raw "e"))
