import Core.Dsl.DefAlias
import Core.Dsl.DefProperty
import MIR.Body
import PCG.PcgDomainData

defAlias AnalysisResults
    (.text "ar",
     .text "AnalysisResults")
  "Per-body Analysis Results"
  (doc! "Analysis results \
    $_ar_ ∈ _AnalysisResults_$ \
    bundle the per-block #PcgDomainData lists produced by a \
    single sweep of `PcgData.analyzeBody`: one entry per \
    basic block, keyed by #BasicBlockIdx.")
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
    l↦stmtIdx < (mapAt ar l↦block)·length

defAlias ProgAnalysisResults
    (.text "par",
     .text "ProgAnalysisResults")
  "Whole-program Analysis Results"
  (doc! "Program analysis results \
    $_par_ ∈ _ProgAnalysisResults_$ \
    bundle the per-body #AnalysisResults produced by \
    running #[analyzeBody] on every function in a program: \
    one entry per #Body.")
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
    contains (mapAt par b) l
