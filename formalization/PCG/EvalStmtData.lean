import Core.Dsl.DefStruct

defStruct EvalStmtData {T}
    (.doc (.plain "esd"),
     .doc (.plain "EvalStmtData"))
  "Evaluation Statement Data"
  (.seq [
    .plain "An evaluation-statement data record ",
    Doc.defMath (.doc (.plain "esd"))
      (.doc (.plain "EvalStmtData")) ["T"],
    .plain " bundles four values of type ",
    .math (.doc (.plain "T")),
    .plain ", one for each ",
    .code "EvalStmtPhase",
    .plain ": before and after the operands are evaluated, \
     and before and after the main effect of the statement. \
     The element type ",
    .math (.doc (.plain "T")),
    .plain " is a parameter of the definition so the same \
     record can be reused for different per-phase payloads."])
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
