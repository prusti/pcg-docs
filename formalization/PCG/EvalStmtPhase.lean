import Core.Dsl.DefEnum

defEnum EvalStmtPhase (.raw "\\varphi", .raw "EvalStmtPhase")
  "Evaluation Statement Phases"
  "A phase of statement evaluation at which the PCG state is \
   observed. Each MIR statement is analysed in four phases: \
   before and after the operands are evaluated, and before and \
   after the main effect of the statement."
where
  | preOperands
    "Before the operands of the statement are evaluated."
    (.doc (.code "PreOperands"))
  | postOperands
    "After the operands of the statement have been evaluated."
    (.doc (.code "PostOperands"))
  | preMain
    "Before the main effect of the statement is applied."
    (.doc (.code "PreMain"))
  | postMain
    "After the main effect of the statement has been applied."
    (.doc (.code "PostMain"))
