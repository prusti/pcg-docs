import OpSem.Machine

defEnum ValueExpr (.raw "ve", .cal (.raw "VE"))
  "Value Expressions"
  (.plain "A MIR value expression that evaluates to a runtime \
   value of a given type.")
where
  | tuple (exprs : List ValueExpr) (ty : Ty)
    "A tuple expression: a list of sub-expressions together \
     with the tuple type."
    (.text "tuple ", #exprs (.raw "\\bar{e}"),
     .text " : ", #ty)
  deriving Repr, BEq, Hashable

namespace Machine

defFn evalValue (.plain "evalValue")
  (doc! "Evaluate a value expression to a runtime value. Currently only the tuple case is \
    implemented; the function will be extended as additional value expressions are introduced.")
  (e "The value expression." : ValueExpr)
  : Value where
  | .tuple exprs _ =>
      Value.tuple (exprs ·map evalValue)

defFn evalTuple (.plain "evalTuple")
  (doc! "Evaluate a tuple value expression: recursively invoke `evalValue` on each sub-expression \
    and wrap the results in #Value.tuple.")
  (exprs "The sub-expressions." : List ValueExpr)
  (ty "The tuple type." : Ty)
  : Value :=
    Value.tuple (exprs ·map evalValue)

end Machine
