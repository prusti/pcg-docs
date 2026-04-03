import Shared.DefEnum

defEnum Capability (.italic (.text "c"))
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capabiility"
    (.bold (.text "∅"))
  | exclusive
    "Exclusive "
    (.bold (.text "E"))
  | read
    "Read"
    (.bold (.text "R"))
  | write
    "Write"
    (.bold (.text "W"))
  | shallowExclusive
    "Shallow exclusive"
    (.bold (.text "e"))
