import Core.Dsl.DefEnum
import MIR.Place
import PCG.MaybeLabelledPlace

defEnum PcgPlace {P}
    (.hat (.raw "p"), .doc (.plain "PcgPlace"))
  "PCG Places"
  (.plain "A PCG place is either a maybe-labelled place or a \
   remote place of the form remote(l), where l is a MIR local. \
   The place set P is a parameter of the definition and is \
   propagated to the underlying MaybeLabelledPlace.")
where
  | maybeLabelled (mlp : MaybeLabelledPlace P)
    "A maybe-labelled place drawn from the MaybeLabelledPlace \
     set over the parameter P."
    (#mlp (.widetilde (.raw "p")))
  | remote (l : Local)
    "A remote place naming a MIR local from the caller."
