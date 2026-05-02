import Core.Dsl.DefEnum

defEnum EvalStmtPhase (.raw "\\varphi", .raw "EvalStmtPhase")
  "Evaluation Statement Phases"
  (doc! "An evaluation statement phase \
    $\\varphi ∈ _EvalStmtPhase_$ \
    identifies one of the four phases at which the PCG state \
    is observed during a MIR statement: before and after the \
    operands are evaluated, and before and after the main \
    effect of the statement.")
where
  | preOperands
    "Before operands."
    (.doc (.code "PreOperands"))
  | postOperands
    "After operands."
    (.doc (.code "PostOperands"))
  | preMain
    "Before the main effect."
    (.doc (.code "PreMain"))
  | postMain
    "After the main effect."
    (.doc (.code "PostMain"))
  deriving DecidableEq, BEq, Repr, Hashable
