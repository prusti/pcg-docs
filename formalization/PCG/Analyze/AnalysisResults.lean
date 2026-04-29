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

defAlias ProgramAnalysisResults
    (.text "par",
     .text "ProgramAnalysisResults")
  "Whole-program Analysis Results"
  (.seq [
    .plain "Program analysis results ",
    Doc.defMath (.text "par")
      (.text "ProgramAnalysisResults"),
    .plain " bundle the per-body ", .code "AnalysisResults",
    .plain " produced by running ", .code "analyzeBody",
    .plain " on every function in a program: one entry per \
     ", .code "Body", .plain "."])
  := Map Body AnalysisResults

defProperty programContains (.plain "programContains")
  short (parDoc, bDoc, lDoc) =>
    (.math (.seq [.doc lDoc,
                  .sym .setContains,
                  .doc parDoc, .raw "[",
                  .doc bDoc, .raw "]"]))
  long (parDoc, bDoc, lDoc) =>
    (.seq [bDoc, .plain " is a key of ", parDoc,
           .plain ", and ", lDoc, .plain " is contained in \
           the per-body analysis results that ", parDoc,
           .plain " stores under ", bDoc])
  (par "The program analysis results."
      : ProgramAnalysisResults)
  (b "The function body." : Body)
  (l "The location." : Location)
  displayed (#l, .sym .setContains, #par, .raw "[", #b,
             .raw "]")
  :=
    b ∈ par ∧
    contains ‹mapAt ‹par, b›, l›
