import Core.Dsl.DefEnum
import MIR.Body

defEnum AnalysisObject (.raw "ao", .raw "AnalysisObject")
  "Analysis Objects"
  (.seq [
    .plain "An analysis object ",
    Doc.defMath (.raw "ao") (.raw "AnalysisObject"),
    .plain " is the program element at which the PCG \
     analysis observes a basic block: either a MIR \
     statement or a MIR terminator."])
where
  | stmt (s : Statement)
    "A MIR statement."
  | terminator (t : Terminator)
    "A MIR terminator."
  deriving Repr, BEq, Hashable
