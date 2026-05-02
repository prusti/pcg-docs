import Core.Dsl.DefEnum
import MIR.Place
import PCG.Nodes.MaybeLabelled

defEnum PcgPlace {P}
    (.hat (.raw "p"), .text "PcgPlace")
  "PCG Places"
  (doc! "A PCG place \
    $\\hat\{p} ∈ _PcgPlace_ _P_$ \
    is either a maybe-labelled place over the place set \
    $#P$, or a remote place naming a MIR local from the \
    caller.")
where
  | maybeLabelled (mlp : MaybeLabelled P)
    "A maybe-labelled place."
    (#mlp (.widetilde (.raw "p")))
  | remote (l : Local)
    "A remote place."
  deriving DecidableEq, BEq, Repr, Hashable
