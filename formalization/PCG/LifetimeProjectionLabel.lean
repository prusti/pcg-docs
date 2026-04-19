import Core.Dsl.DefEnum
import PCG.SnapshotLocation

defEnum LifetimeProjectionLabel
    (.raw "\\ell", .doc (.plain "LifetimeProjectionLabel"))
  "Lifetime Projection Labels"
  (.plain "A label attached to a lifetime projection: either \
   a snapshot location identifying when the projection was \
   taken, or the placeholder FUTURE label identifying a \
   projection that refers to a future program point.")
where
  | location (sl : SnapshotLocation)
    "A label identifying the snapshot location at which the \
     lifetime projection was taken."
    (#sl)
  | future
    "The placeholder FUTURE label, used for projections that \
     refer to a future program point."
    (.doc (.code "FUTURE"))
