import MIR.Body
import PCG.EvalStmtPhase

defStruct AnalysisLocation (.doc (.plain "al"),
    .doc (.plain "AnalysisLocation"))
  "Analysis Locations"
  (.seq [
    .plain "An analysis location ",
    Doc.defMath (.doc (.plain "al"))
      (.doc (.plain "AnalysisLocation")),
    .plain " identifies a program point at which the PCG \
     state is observed: a MIR location paired with the \
     evaluation phase of the statement at that location."])
where
  | location "MIR location." : Location
  | phase "Evaluation phase." : EvalStmtPhase
