import Core.Dsl.DefEnum
import PCG.Nodes.SnapshotLocation

defEnum LPLabel
    (.cal (.raw "L"), .text "LPLabel")
  "Lifetime Projection Labels"
  (doc! "A lifetime projection label \
    {.math (.seq [symDoc, .sym .setContains, setDoc])} \
    is either a snapshot location identifying when the \
    projection was taken, or the placeholder \
    {Doc.math (.doc (.code "FUTURE"))} label, used for \
    projections that refer to a future program point.")
where
  | location (sl : SnapshotLocation)
    "A snapshot location."
    (sl)
  | future
    "The FUTURE placeholder."
    (MathDoc.doc (.code "FUTURE"))
