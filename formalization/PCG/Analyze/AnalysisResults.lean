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
    .math (.seq [.text "ar", .sym .setContains, .text "AnalysisResults"]),
    .plain " bundle the per-block ", Doc.refLinkOf @PcgDomainData "PcgDomainData",
    .plain " lists produced by a single sweep of ",
    .code "PcgData.analyzeBody",
    .plain ": one entry per basic block, keyed by ",
    Doc.refLinkOf @BasicBlockIdx "BasicBlockIdx", .plain "."])
  := Map BasicBlockIdx (List PcgDomainData)

defProperty contains (.plain "contains")
  short
    (.math (.seq [.doc l,
                  .sym .setContains,
                  .doc ar]))
  long
    (doc! "the basic block of {l} is a key of {ar}, and the \
      statement index of {l} is less than the length of the \
      per-block list {ar} stores at that key")
  (ar "The analysis results." : AnalysisResults)
  (l "The location." : Location)
  displayed (#l, .sym .setContains, #ar)
  :=
    l↦block ∈ ar ∧
    l↦stmtIdx < (mapAt ‹ar, l↦block›)·length

defAlias ProgAnalysisResults
    (.text "par",
     .text "ProgAnalysisResults")
  "Whole-program Analysis Results"
  (.seq [
    .plain "Program analysis results ",
    .math (.seq [.text "par", .sym .setContains, .text "ProgAnalysisResults"]),
    .plain " bundle the per-body ", Doc.refLinkOf @AnalysisResults "AnalysisResults",
    .plain " produced by running ", Doc.refLinkByName "analyzeBody",
    .plain " on every function in a program: one entry per \
     ", Doc.refLinkOf @Body "Body", .plain "."])
  := Map Body AnalysisResults

defProperty programContains (.plain "programContains")
  short
    (.math (.seq [.doc l,
                  .sym .setContains,
                  .doc par, .raw "[",
                  .doc b, .raw "]"]))
  long
    (doc! "{b} is a key of {par}, and {l} is contained in \
      the per-body analysis results that {par} stores under \
      {b}")
  (par "The program analysis results."
      : ProgAnalysisResults)
  (b "The function body." : Body)
  (l "The location." : Location)
  displayed (#l, .sym .setContains, #par, .raw "[", #b,
             .raw "]")
  :=
    b ∈ par ∧
    contains ‹mapAt ‹par, b›, l›
