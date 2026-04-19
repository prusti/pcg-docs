import MIR.Body
import PCG.AnalysisLocation

defEnum SnapshotLocation (.doc (.plain "sl"),
    .doc (.plain "SnapshotLocation"))
  "Snapshot Locations"
  "A program point at which a PCG snapshot is taken: either \
   immediately before an analysis location, at the end of a \
   basic block, or at the head of a loop."
where
  | before (al : AnalysisLocation)
    "A snapshot taken immediately before an analysis location."
    (.doc (.plain "Before"), .sym .lparen,
     #al, .sym .rparen)
  | after (bb : BasicBlockIdx)
    "A snapshot taken at the end of a basic block."
    (.doc (.plain "After"), .sym .lparen,
     #bb, .sym .rparen)
  | loop (bb : BasicBlockIdx)
    "A snapshot taken at the head of a loop."
    (.doc (.plain "Loop"), .sym .lparen,
     #bb, .sym .rparen)
