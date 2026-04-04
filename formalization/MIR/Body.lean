import MIR.Place

defStruct BasicBlockIdx (.text "bb")
  "An index into the list of basic blocks."
where
  | index "The basic block index." : Nat

defEnum Operand (.italic (.text "o"))
  "An operand in a MIR statement or terminator."
where
  | copy (place : Place)
    "Copy the value at a place."
    (.text "copy ", #place)
  | move (place : Place)
    "Move the value out of a place."
    (.text "move ", #place)
  deriving Repr

defEnum Rvalue (.italic (.text "rv"))
  "A right-hand side value in an assignment."
where
  | use (operand : Operand)
    "Use an operand directly."
    (.text "use(", #operand, .text ")")
  | ref (region : Region) (mutability : Mutability)
      (place : Place)
    "Create a reference to a place."
    (.text "\\&", #region, .text " ",
     #mutability, .text " ", #place)
  deriving Repr

defEnum Statement (.italic (.text "s"))
  "A MIR statement within a basic block."
where
  | assign (lhs : Place) (rhs : Rvalue)
    "Assign an rvalue to a place."
    (#lhs, .text " := ", #rhs)
  | storageLive (lcl : Local)
    "Mark a local's storage as live."
    (.text "StorageLive(", #lcl, .text ")")
  | storageDead (lcl : Local)
    "Mark a local's storage as dead."
    (.text "StorageDead(", #lcl, .text ")")
  deriving Repr

defEnum Terminator (.italic (.text "t"))
  "A basic block terminator."
where
  | goto (target : BasicBlockIdx)
    "Unconditional jump."
    (.text "goto ", #target)
  | switchInt (operand : Operand)
    "Switch on an integer value."
    (.text "switchInt(", #operand, .text ")")
  | return_
    "Return from the function."
    (.text "return")
  | unreachable
    "Marks unreachable code."
    (.text "unreachable")
  | drop (place : Place) (target : BasicBlockIdx)
    "Drop the value at a place."
    (.text "drop(",
     #place, .text ", ", #target, .text ")")
  deriving Repr

defStruct BasicBlock (.text "B")
  "A basic block: a sequence of statements followed \
   by a terminator."
where
  | statements "The statements in the block."
      : List Statement
  | terminator "The block's terminator." : Terminator
  deriving Repr

defStruct LocalDecls (.text "Δ")
  "Local variable declarations: a type for each local."
where
  | decls "The type of each local variable."
      : List Ty

defStruct Body (.text "body")
  "A MIR function body."
where
  | localDecls "The local variable declarations."
      : LocalDecls
  | basicBlocks "The basic blocks." : List BasicBlock
  deriving Repr
