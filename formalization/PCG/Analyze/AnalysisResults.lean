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
  short
    (.math (.seq [.doc l,
                  .sym .setContains,
                  .doc ar]))
  long
    (.seq [.plain "the basic block of ", l,
           .plain " is a key of ", ar,
           .plain ", and the statement index of ", l,
           .plain " is less than the length of the per-block \
                   list ", ar, .plain " stores at that key"])
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
    Doc.defMath (.text "par")
      (.text "ProgAnalysisResults"),
    .plain " bundle the per-body ", .code "AnalysisResults",
    .plain " produced by running ", Doc.refLinkByName "analyzeBody",
    .plain " on every function in a program: one entry per \
     ", .code "Body", .plain "."])
  := Map Body AnalysisResults

defProperty programContains (.plain "programContains")
  short
    (.math (.seq [.doc l,
                  .sym .setContains,
                  .doc par, .raw "[",
                  .doc b, .raw "]"]))
  long
    (.seq [b, .plain " is a key of ", par,
           .plain ", and ", l, .plain " is contained in \
           the per-body analysis results that ", par,
           .plain " stores under ", b])
  (par "The program analysis results."
      : ProgAnalysisResults)
  (b "The function body." : Body)
  (l "The location." : Location)
  displayed (#l, .sym .setContains, #par, .raw "[", #b,
             .raw "]")
  :=
    b ∈ par ∧
    contains ‹mapAt ‹par, b›, l›
