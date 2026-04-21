import Core.Dsl.DefStruct

defStruct UnpackEdge {N}
    (.doc (.plain "ue"), .doc (.plain "UnpackEdge"))
  "Unpack Edges"
  (.seq [
    .plain "An unpack edge ",
    Doc.defMath (.doc (.plain "ue"))
      (.doc (.plain "UnpackEdge")) ["N"],
    .plain " connects an owned base place to its expansion: a \
     list of owned places corresponding to the components of \
     the base. Each place in the expansion is itself owned. \
     For example, if a place has fields p.f and p.g, an unpack \
     edge with base p and expansion [p.f, p.g] represents the \
     hyperedge from the base to its two component places. The \
     place set ",
    .math (.doc (.plain "N")),
    .plain " is a parameter of the definition so the same \
     constructor can be reused with different underlying place \
     representations. Unpack edges are also used for \
     dereferences of Box-typed places; dereferences of \
     reference-typed places use Deref Edges \
     instead."])
where
  | base "The node that is unpacked"
      : N
  | expansion "The expansion of the base"
      : List N
  deriving BEq, Repr, Hashable
