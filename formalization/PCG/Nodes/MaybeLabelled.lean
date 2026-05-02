import Core.Dsl.DefEnum
import PCG.Nodes.SnapshotLocation

defEnum MaybeLabelled {P}
    (.widetilde (.raw "p"),
     .text "MaybeLabelled")
  "Maybe-Labelled Places"
  (.seq [
    .plain "A maybe-labelled place ",
    .math (.seq [.widetilde (.raw "p"), .sym .setContains, .text "MaybeLabelled", .sym .space, .raw "P"]),
    .plain " is either a current (unlabelled) place drawn \
     from the parameter set ",
    .math (.text "P"),
    .plain ", or a place labelled with the snapshot \
     location at which it was taken."])
where
  | current (p : P)
    "A current (unlabelled) place."
    (#p (.raw "p"))
  | labelled (p : P) (sl : SnapshotLocation)
    "A labelled place."
    (#p (.raw "p"), .text " ",
     .doc (.code "at"), .text " ", #sl)
  deriving DecidableEq, BEq, Repr, Hashable
