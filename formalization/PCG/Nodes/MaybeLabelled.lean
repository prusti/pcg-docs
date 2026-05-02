import Core.Dsl.DefEnum
import PCG.Nodes.SnapshotLocation

defEnum MaybeLabelled {P}
    (.widetilde (.raw "p"),
     .text "MaybeLabelled")
  "Maybe-Labelled Places"
  (doc! "A maybe-labelled place \
    $\\widetilde\{p} ∈ _MaybeLabelled_ _P_$ \
    is either a current (unlabelled) place drawn from the \
    parameter set $#P$, or a place labelled with the \
    snapshot location at which it was taken.")
where
  | current (p : P)
    "A current (unlabelled) place."
    (MathDoc.raw "p")
  | labelled (p : P) (sl : SnapshotLocation)
    "A labelled place."
    (mathdoc! "p {(MathDoc.doc (.code "at"))} {sl}")
  deriving DecidableEq, BEq, Repr, Hashable
