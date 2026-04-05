import Core.Dsl.DefEnum

defEnum Capability (.math (.var "c"))
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capabiility"
    (.math (.doc (.bold (.text "∅"))))
  | exclusive
    "Exclusive "
    (.math (.doc (.bold (.text "E"))))
  | read
    "Read"
    (.math (.doc (.bold (.text "R"))))
  | write
    "Write"
    (.math (.doc (.bold (.text "W"))))
  | shallowExclusive
    "Shallow exclusive"
    (.math (.doc (.bold (.text "e"))))
