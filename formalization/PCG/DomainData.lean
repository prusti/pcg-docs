import Core.Dsl.DefStruct
import PCG.EvalStmtData

defStruct DomainData {T}
    (.text "dd",
     .text "DomainData")
  "Domain Data"
  (.seq [
    .plain "A domain-data record ",
    Doc.defMath (.text "dd")
      (.text "DomainData") ["T"],
    .plain " bundles the per-program-point dataflow state of \
     a single basic block: the value on entry, plus an ",
    Doc.refLinkOf @EvalStmtData "EvalStmtData",
    .plain " carrying the four per-phase values produced as \
     the analysis steps through each statement of the block."])
where
  | entryState "Value on entry to the basic block."
      : T
  | states "Per-phase values produced while stepping the block."
      : EvalStmtData T
  deriving Repr
