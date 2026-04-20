import Core.Dsl.DefEnum
import MIR.ConstValue
import PCG.Nodes.PcgPlace

defEnum PcgLifetimeProjectionBase {P}
    (.doc (.plain "b"),
     .doc (.plain "PcgLifetimeProjectionBase"))
  "PCG Lifetime Projection Bases"
  (.seq [
    .plain "A PCG lifetime projection base ",
    Doc.defMath (.doc (.plain "b"))
      (.doc (.plain "PcgLifetimeProjectionBase")) ["P"],
    .plain " is either a constant value or a PCG place over \
     the place set ",
    .math (.doc (.plain "P")),
    .plain "."])
where
  | const (cv : ConstValue)
    "A constant value."
    (#cv)
  | place (p : PcgPlace P)
    "A PCG place."
    (#p)
  deriving BEq, Repr, Hashable
