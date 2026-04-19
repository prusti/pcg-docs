import MIR.Body
import PCG.AnalysisLocation

defEnum SnapshotLocation (.doc (.plain "sl"),
    .doc (.plain "SnapshotLocation"))
  "Snapshot Locations"
  (.plain "A program point at which a PCG snapshot is taken: \
   either immediately before an analysis location, at the end \
   of a basic block, or at the head of a loop.")
where
  | before (al : AnalysisLocation)
    "A snapshot taken immediately before an analysis location."
  | after (bb : BasicBlockIdx)
    "A snapshot taken at the end of a basic block."
  | loop (bb : BasicBlockIdx)
    "A snapshot taken at the head of a loop."
