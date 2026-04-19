import Core.Dsl.DefEnum
import PCG.SnapshotLocation

defEnum MaybeLabelledPlace {P}
    (.raw "\\widetilde{p}", .doc (.plain "MaybeLabelledPlace"))
  "Maybe-Labelled Places"
  (.plain "A maybe-labelled place is either a current place \
   or a place labelled with a snapshot location. The place \
   set P is a parameter of the definition (similar to the \
   base and index sets of a LifetimeProjection), so the same \
   constructor can be reused with different underlying place \
   representations.")
where
  | current (p : P)
    "A current (unlabelled) place drawn from the parameter \
     set P."
    (#p (.raw "p"))
  | labelled (p : P) (sl : SnapshotLocation)
    "A place from the parameter set P together with the \
     snapshot location it is labelled at."
    (#p (.raw "p"), .doc (.plain " "),
     .doc (.code "at"), .doc (.plain " "), #sl)
