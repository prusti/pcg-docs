import Shared.DefEnum

defEnum Capability
  "A capability describes the actions permitted on a \
   place at a particular program point."
where
  | exclusive
    "Can be read, written, or mutably borrowed."
    "E"
  | read
    "Can be read from; shared borrows can also be created."
    "R"
  | write
    "The place can be written to."
    "W"
  | shallowExclusive
    "Intermediate state when converting a raw pointer to a Box."
    "e"
