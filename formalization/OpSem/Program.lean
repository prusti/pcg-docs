import MIR.Body

defStruct Program (.raw "\\Pi", .doc (.plain "Program"))
  "Programs"
  "A program is a list of basic blocks."
where
  | blocks "The basic blocks." : List BasicBlock
  deriving Repr, Hashable
