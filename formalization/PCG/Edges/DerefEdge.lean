import Core.Dsl.DefStruct
import PCG.Nodes.LocalLifetimeProjection
import PCG.Nodes.MaybeLabelled

defStruct DerefEdge {P}
    (.doc (.plain "de"), .doc (.plain "DerefEdge"))
  "Deref Edges"
  (.seq [
    .plain "A deref edge ",
    Doc.defMath (.doc (.plain "de"))
      (.doc (.plain "DerefEdge")) ["P"],
    .plain " connects a reference-typed blocked place to the \
     place obtained by dereferencing it, together with the \
     lifetime projection of the blocked place that is blocked \
     by this edge. The blocked lifetime projection is \
     generally unlabelled when the blocked place is a shared \
     reference, and labelled with the MIR location of the \
     dereference when the blocked place is a mutable \
     reference. Deref edges are used for dereferences of \
     reference-typed places; dereferences of Box-typed places \
     use Unpack Edges instead."])
where
  | blockedPlace "The reference-typed place that is blocked."
      : MaybeLabelled P
  | derefPlace "The place obtained by dereferencing the \
      blocked place."
      : MaybeLabelled P
  | blockedLifetimeProjection "The lifetime projection of \
      the blocked place that is blocked by this edge."
      : LocalLifetimeProjection P
  deriving BEq, Repr, Hashable
