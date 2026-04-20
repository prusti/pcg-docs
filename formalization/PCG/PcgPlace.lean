import Core.Dsl.DefEnum
import MIR.Place
import PCG.MaybeLabelledPlace

defEnum PcgPlace {P}
    (.hat (.raw "p"), .doc (.plain "PcgPlace"))
  "PCG Places"
  (.seq [
    .plain "A PCG place ",
    Doc.defMath (.hat (.raw "p")) (.doc (.plain "PcgPlace")),
    .plain " is either a maybe-labelled place over the place \
     set ",
    .math (.doc (.plain "P")),
    .plain ", or a remote place naming a MIR local from the \
     caller."])
where
  | maybeLabelled (mlp : MaybeLabelledPlace P)
    "A maybe-labelled place."
    (#mlp (.widetilde (.raw "p")))
  | remote (l : Local)
    "A remote place."
