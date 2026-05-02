import Core.Dsl.DefEnum
import MIR.ConstValue
import PCG.Nodes.PcgPlace

defEnum PcgLifetimeProjectionBase {P}
    (.text "b",
     .text "PcgLifetimeProjectionBase")
  "PCG Lifetime Projection Bases"
  (doc! "A PCG lifetime projection base \
    $_b_ ∈ _PcgLifetimeProjectionBase_ _P_$ \
    is either a constant value or a PCG place over the \
    place set $#P$.")
where
  | const (cv : ConstValue)
    "A constant value."
    (#cv)
  | place (p : PcgPlace P)
    "A PCG place."
    (#p)
  deriving BEq, Repr, Hashable
