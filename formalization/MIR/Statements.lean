import MIR.Place
import MIR.ConstValue
import Core.Dsl.DefFn

defEnum Operand (.raw "o", .raw "O")
  "Operands"
  (.plain "An operand in a MIR statement or terminator.")
where
  | copy (place : Place)
    "Copy the value at a place."
  | move (place : Place)
    "Move the value out of a place."
  | const (val : ConstValue)
    "A constant value."
  deriving Repr, BEq, Hashable

namespace Operand

defFn operandPlace (.plain "operandPlace")
  (.plain "Extract the place from an operand, if any.")
  (o "The operand." : Operand)
  : Option Place where
  | .copy p => Some p
  | .move p => Some p
  | .const _ => None

end Operand

defEnum Rvalue (.raw "rv", .raw "Rv")
  "Rvalues"
  (.plain "A right-hand side value in an assignment.")
where
  | use (operand : Operand)
    "Use an operand directly."
  | ref (region : Region) (mutability : Mutability)
      (place : Place)
    "Create a reference to a place."
    (.doc (.code "&"), #region, .text " ",
     #mutability, .text " ", #place)
  deriving Repr, BEq, Hashable

namespace Rvalue

defFn rvaluePlace (.plain "rvaluePlace")
  (.plain "Extract the place from an rvalue, if any.")
  (rv "The rvalue." : Rvalue)
  : Option Place where
  | .use o => o·operandPlace
  | .ref _ _ p => Some p

defFn rvalueOperands (.plain "rvalueOperands")
  (.plain "The set of operands used by an rvalue.")
  (rv "The rvalue." : Rvalue)
  : Set Operand where
  | .use o => ⦃o⦄
  | .ref _ _ _ => ∅

end Rvalue

defEnum Statement (.raw "s", .raw "S")
  "Statements"
  (.plain "A MIR statement within a basic block.")
where
  | assign (lhs : Place) (rhs : Rvalue)
    "Assign an rvalue to a place."
    (#lhs, .text " := ", #rhs)
  | storageLive (lcl : Local)
    "Mark a local's storage as live."
  | storageDead (lcl : Local)
    "Mark a local's storage as dead."
  deriving Repr, BEq, Hashable

namespace Statement

defFn statementPlaces (.plain "statementPlaces")
  (.plain "Extract all places referenced by a statement.")
  (s "The statement." : Statement)
  : Set Place where
  | .assign lhs rhs =>
      ⦃lhs⦄ ∪ (rhs·rvaluePlace)·toSet
  | .storageLive _ => ∅
  | .storageDead _ => ∅

defFn stmtOperands (.plain "stmtOperands")
  (.plain "The set of operands used by a statement.")
  (s "The statement." : Statement)
  : Set Operand where
  | .assign _ rhs => rhs·rvalueOperands
  | .storageLive _ => ∅
  | .storageDead _ => ∅

end Statement
