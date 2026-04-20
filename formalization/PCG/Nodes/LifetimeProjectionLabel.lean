import Core.Dsl.DefEnum
import PCG.Nodes.SnapshotLocation

defEnum LifetimeProjectionLabel
    (.raw "\\ell", .doc (.plain "LifetimeProjectionLabel"))
  "Lifetime Projection Labels"
  (.seq [
    .plain "A lifetime projection label ",
    Doc.defMath (.raw "\\ell")
      (.doc (.plain "LifetimeProjectionLabel")),
    .plain " is either a snapshot location identifying when \
     the projection was taken, or the placeholder ",
    .math (.doc (.code "FUTURE")),
    .plain " label, used for projections that refer to a \
     future program point."])
where
  | location (sl : SnapshotLocation)
    "A snapshot location."
    (#sl)
  | future
    "The FUTURE placeholder."
    (.doc (.code "FUTURE"))
