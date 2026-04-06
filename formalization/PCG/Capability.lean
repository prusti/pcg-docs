import Core.Dsl.DefEnum

defEnum Capability (.math (.var "c"))
  "Capabilities"
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capability"
    (.doc (.bold (.plain "∅")))
  | exclusive
    "Exclusive "
    (.doc (.bold (.plain "E")))
  | read
    "Read"
    (.doc (.bold (.plain "R")))
  | write
    "Write"
    (.doc (.bold (.plain "W")))
  | shallowExclusive
    "Shallow exclusive"
    (.doc (.bold (.plain "e")))
