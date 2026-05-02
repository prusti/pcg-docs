import Core.Dsl.DefEnum
import Core.Dsl.DefProperty
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

defProperty validAnalysisObject (.plain "validAnalysisObject")
  short
    (.seq [ao, .plain " is a valid analysis object in ", body])
  long
    (.seq [.plain "either ", ao,
           .plain " wraps a statement that is valid in ", body,
           .plain ", or it wraps a terminator that is valid \
           in ", body])
  (body "The function body." : Body)
  (ao "The analysis object." : AnalysisObject)
  :=
    match ao with
    | .stmt s => validStatement ‹body, s›
    | .terminator t => validTerminator ‹body, t›
    end
