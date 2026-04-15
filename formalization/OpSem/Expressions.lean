import OpSem.Machine
import OpSem.RuntimePlace

/-- Look up a key in a HashMap. -/
def mapGet {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) : Option ν :=
  m.get? k

namespace Machine

defFn evalLocal (.plain "evalLocal")
  (.seq [.plain "Evaluate a local variable, returning its \
    runtime place. Returns ", .code "None",
    .plain " if the local is dead."])
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  : Option RuntimePlace begin
  let ptr ← mapGet ‹machine↦locals, lcl›
  return Some (RuntimePlace⟨ptr⟩)

end Machine

defEnum ValueExpr (.raw "ve", .cal (.raw "VE"))
  "Value Expressions"
  "A MIR value expression that evaluates to a runtime \
   value of a given type."
where
  | tuple (exprs : List ValueExpr) (ty : Ty)
    "A tuple expression: a list of sub-expressions together \
     with the tuple type."
    (.doc (.plain "tuple "), #exprs (.raw "\\bar{e}"),
     .doc (.plain " : "), #ty)
  deriving Repr, BEq, Hashable

namespace Machine

defFn evalValue (.plain "evalValue")
  (.seq [.plain "Evaluate a value expression to a runtime \
    value. Currently only the tuple case is implemented; \
    the function will be extended as additional value \
    expressions are introduced."])
  (e "The value expression." : ValueExpr)
  : Value where
  | .tuple exprs _ =>
      Value.tuple‹exprs ·map evalValue›

defFn evalTuple (.plain "evalTuple")
  (.seq [.plain "Evaluate a tuple value expression: \
    recursively invoke ", .code "evalValue",
    .plain " on each sub-expression and wrap the results \
    in ", .code "Value.tuple", .plain "."])
  (exprs "The sub-expressions." : List ValueExpr)
  (ty "The tuple type." : Ty)
  : Value :=
    Value.tuple‹exprs ·map evalValue›

end Machine
