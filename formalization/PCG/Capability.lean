import Shared.DefEnum

defEnum Capability (.italic (.text "c"))
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | none
    "No capability; the place cannot be accessed."
    (.bold (.text "∅"))
    (.text "None")
  | exclusive
    "Can be read, written, or mutably borrowed."
    (.bold (.text "E"))
    (.seq [.bold (.text "E"), .text "xclusive"])
  | read
    "Can be read from; shared borrows can also be created."
    (.bold (.text "R"))
    (.seq [.bold (.text "R"), .text "ead"])
  | write
    "The place can be written to."
    (.bold (.text "W"))
    (.seq [.bold (.text "W"), .text "rite"])
  | shallowExclusive
    "Intermediate state when converting a raw pointer to a Box."
    (.bold (.text "e"))
    (.seq
      [.text "Shallow", .bold (.text "E"), .text "xclusive"])
