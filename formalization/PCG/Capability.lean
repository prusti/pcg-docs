import Core.Dsl.DefEnum

defEnum Capability (.raw "c", .raw "C")
  "Capabilities"
  (.seq [
    .plain "A capability ",
    Doc.defMath (.raw "c") (.raw "C"),
    .plain " describes the actions permitted on a place at a \
     particular program point: either no capability (",
    .math (.sym .emptySet),
    .plain "), exclusive (",
    .math (.bold (.raw "E")),
    .plain "), read (",
    .math (.bold (.raw "R")),
    .plain "), write (",
    .math (.bold (.raw "W")),
    .plain "), or shallow exclusive (",
    .math (.bold (.raw "e")),
    .plain ")."])
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
