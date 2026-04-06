import Core.Dsl.DefEnum

defEnum Capability (.raw "c", .raw "C")
  "Capabilities"
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capability"
    (.sym .emptySet)
  | exclusive
    "Exclusive "
    (.bold (.raw "E"))
  | read
    "Read"
    (.bold (.raw "R"))
  | write
    "Write"
    (.bold (.raw "W"))
  | shallowExclusive
    "Shallow exclusive"
    (.bold (.raw "e"))
