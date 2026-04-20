import Core.Dsl.DefEnum
import PCG.Nodes.SnapshotLocation

defEnum MaybeLabelledPlace {P}
    (.widetilde (.raw "p"),
     .doc (.plain "MaybeLabelledPlace"))
  "Maybe-Labelled Places"
  (.seq [
    .plain "A maybe-labelled place ",
    Doc.defMath (.widetilde (.raw "p"))
      (.doc (.plain "MaybeLabelledPlace")) ["P"],
    .plain " is either a current (unlabelled) place drawn \
     from the parameter set ",
    .math (.doc (.plain "P")),
    .plain ", or a place labelled with the snapshot \
     location at which it was taken."])
where
  | current (p : P)
    "A current (unlabelled) place."
    (#p (.raw "p"))
  | labelled (p : P) (sl : SnapshotLocation)
    "A labelled place."
    (#p (.raw "p"), .doc (.plain " "),
     .doc (.code "at"), .doc (.plain " "), #sl)
  deriving DecidableEq, BEq, Repr, Hashable
