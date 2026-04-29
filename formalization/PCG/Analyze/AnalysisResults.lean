import Core.Dsl.DefAlias
import Core.Dsl.DefProperty
import MIR.Body
import PCG.PcgDomainData

defAlias AnalysisResults
    (.text "ar",
     .text "AnalysisResults")
  "Per-body Analysis Results"
  (.seq [
    .plain "Analysis results ",
    Doc.defMath (.text "ar")
      (.text "AnalysisResults"),
    .plain " bundle the per-block ", .code "PcgDomainData",
    .plain " lists produced by a single sweep of ",
    .code "PcgData.analyzeBody",
    .plain ": one entry per basic block, keyed by ",
    .code "BasicBlockIdx", .plain "."])
  := Map BasicBlockIdx (List PcgDomainData)

defProperty contains (.plain "contains")
  short (arDoc, lDoc) =>
    (.math (.seq [.doc lDoc,
                  .sym .setContains,
                  .doc arDoc]))
  long (arDoc, lDoc) =>
    (.seq [.plain "the basic block of ", lDoc,
           .plain " is a key of ", arDoc,
           .plain ", and the statement index of ", lDoc,
           .plain " is less than the length of the per-block \
                   list ", arDoc, .plain " stores at that key"])
  (ar "The analysis results." : AnalysisResults)
  (l "The location." : Location)
  displayed (#l, .sym .setContains, #ar)
  :=
    l↦block ∈ ar ∧
    l↦stmtIdx < (mapAt ‹ar, l↦block›)·length
