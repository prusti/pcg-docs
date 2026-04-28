import Core.Dsl.DefAlias
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
