import MIR.Body
import PCG.Nodes.AnalysisLocation

defEnum SnapshotLocation (.text "sl",
    .text "SnapshotLocation")
  "Snapshot Locations"
  (doc! "A snapshot location \
    {.math (.seq [(.text "sl"), .sym .setContains, (.text "SnapshotLocation")])} \
    is a program point at which a PCG snapshot is taken: \
    either immediately before an analysis location, at the \
    end of a basic block, or at the head of a loop.")
where
  | before (al : AnalysisLocation)
    "Immediately before an analysis location."
  | after (bb : BasicBlockIdx)
    "At the end of a basic block."
  | loop (bb : BasicBlockIdx)
    "At the head of a loop."
  deriving DecidableEq, BEq, Repr, Hashable
