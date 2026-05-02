import Core.Dsl.DefStruct
import PCG.EvalStmtPhase

defStruct EvalStmtData {T}
    (.text "esd",
     .text "EvalStmtData")
  "Evaluation Statement Data"
  (doc! "An evaluation-statement data record \
    {.math (.seq [(.text "esd"), .sym .setContains, (.text "EvalStmtData"), .sym .space, .raw "T"])} \
    bundles four values of type $#T$, one for each \
    #EvalStmtPhase: before and after the operands are \
    evaluated, and before and after the main effect of the \
    statement. The element type $#T$ is a parameter of the \
    definition so the same record can be reused for \
    different per-phase payloads.")
where
  | preOperands "Value before the operands are evaluated."
      : T
  | postOperands "Value after the operands are evaluated."
      : T
  | preMain "Value before the main effect of the statement."
      : T
  | postMain "Value after the main effect of the statement."
      : T
  deriving Repr
