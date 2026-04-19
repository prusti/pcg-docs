import MIR.Body
import PCG.EvalStmtPhase

defStruct AnalysisLocation (.doc (.plain "al"),
    .doc (.plain "AnalysisLocation"))
  "Analysis Locations"
  "An analysis location identifies a program point at which \
   the PCG state is observed: a MIR location paired with the \
   evaluation phase of the statement at that location."
where
  | location "The MIR location." : Location
  | phase "The evaluation phase of the statement." : EvalStmtPhase
