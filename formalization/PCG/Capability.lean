import Core.Dsl.DefEnum

defEnum Capability (.math (.var "c"))
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capability"
    (.doc (.bold (.text "∅")))
  | exclusive
    "Exclusive "
    (.doc (.bold (.text "E")))
  | read
    "Read"
    (.doc (.bold (.text "R")))
  | write
    "Write"
    (.doc (.bold (.text "W")))
  | shallowExclusive
    "Shallow exclusive"
    (.doc (.bold (.text "e")))
