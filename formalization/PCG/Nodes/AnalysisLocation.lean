import MIR.Body
import PCG.EvalStmtPhase

defStruct AnalysisLocation (.text "al",
    .text "AnalysisLocation")
  "Analysis Locations"
  (.seq [
    .plain "An analysis location ",
    Doc.defMath (.text "al")
      (.text "AnalysisLocation"),
    .plain " identifies a program point at which the PCG \
     state is observed: a MIR location paired with the \
     evaluation phase of the statement at that location."])
where
  | location "MIR location." : Location
  | phase "Evaluation phase." : EvalStmtPhase
  deriving DecidableEq, BEq, Repr, Hashable
