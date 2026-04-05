import MIR.Ty

defStruct Local (.math (.var "l"))
  "A local variable in the MIR, identified by index."
where
  | index "The local variable index." : Nat

defStruct FieldIdx (.math (.var "f"))
  "A field index within a struct or tuple."
where
  | index "The field index." : Nat

defStruct VariantIdx (.math (.var "V"))
  "A variant index within an enum."
where
  | index "The variant index." : Nat

defEnum ProjElem (.math (.var "π"))
  "A projection element applied to a place. \
   See definitions/places.md."
where
  | deref
    "Dereference a pointer or reference."
    (.doc (.code "*"))
  | field (idx : FieldIdx) (ty : Ty)
    "Access a field by index."
    (.doc (.plain "."),
     #idx,
     .doc (.plain " : "),
     #ty)
  | index (idx : Local)
    "Index into an array or slice."
    (.sym .lbracket,
     #idx,
     .sym .rbracket)
  | downcast (variant : VariantIdx)
    "Downcast an enum to a specific variant."
    (.doc (.plain "@"),
     #variant)
  deriving Repr, BEq, Hashable

defStruct Place (.math (.var "p"))
  "A place in the MIR: a local with a projection. \
   See definitions/places.md."
where
  | base "The base local variable." : Local
  | projection "The list of projection elements."
      : List ProjElem
  deriving Repr, BEq, Hashable
