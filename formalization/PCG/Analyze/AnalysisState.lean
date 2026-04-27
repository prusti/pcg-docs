import Core.Dsl.DefStruct
import MIR.Body
import PCG.Analyze.AnalysisResults
import PCG.PcgData
import PCG.PcgDomainData

defStruct AnalysisState
    (.doc (.plain "as"),
     .doc (.plain "AnalysisState"))
  "Per-body Analysis State"
  (.seq [
    .plain "An analysis state ",
    Doc.defMath (.doc (.plain "as"))
      (.doc (.plain "AnalysisState")),
    .plain " bundles the in-progress per-block analysis \
     results with the entry-state map populated by \
     forward propagation. When a block ", .code "bb",
    .plain " is processed, its result is recorded in ",
    .code "results", .plain " and its post-main exit state \
     is joined into ", .code "entryStates",
    .plain " for every successor of ", .code "bb",
    .plain ". Successor entries that have not yet received \
     a contribution simply become that contribution; \
     subsequent contributions are folded in via ",
    .code "PcgData.join", .plain "."])
where
  | results "Per-block analysis results recorded so far."
      : AnalysisResults
  | entryStates "Pending entry state for each block, joined \
       from already-processed predecessors."
      : Map BasicBlockIdx (PcgData Place)
  deriving Repr
