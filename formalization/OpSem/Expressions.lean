import OpSem.Machine

defEnum ValueExpr (.raw "ve", .cal (.raw "VE"))
  "Value Expressions"
  (.plain "A MIR value expression that evaluates to a runtime \
   value of a given type.")
where
  | tuple (exprs : List ValueExpr) (ty : Ty)
    "A tuple expression: a list of sub-expressions together \
     with the tuple type."
    (mathdoc! "#tuple {(MathDoc.raw "\\bar{e}")} : {ty}")
  deriving Repr, BEq, Hashable

namespace Machine

defFn evalValue (.plain "evalValue")
  (doc! "Evaluate a value expression to a runtime value. Currently only the tuple case is \
    implemented; the function will be extended as additional value expressions are introduced.")
  (e "The value expression." : ValueExpr)
  : Value where
  | .tuple exprs _ =>
      Value.tuple (exprs ·map evalValue)

end Machine
