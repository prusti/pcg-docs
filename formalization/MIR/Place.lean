import MIR.Ty

defStruct Local (.raw "l", .raw "L")
  "Locals"
  "A local {def} is a variable in the MIR, identified by index."
  constructor "LocalIdx"
where
  | index "The local variable index." : Nat

defStruct FieldIdx (.raw "f", .raw "F")
  "Field Indices"
  "A field index within a struct or tuple."
where
  | index "The field index." : Nat

defStruct VariantIdx (.raw "V",
    .doc (.plain "VariantIdx"))
  "Variant Indices"
  "A variant index within an enum."
where
  | index "The variant index." : Nat

defEnum ProjElem (.raw "π", .raw "Π")
  "Projection Elements"
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

defStruct Place (.raw "p", .raw "P")
  "Places"
  "A place in the MIR: a local with a projection. \
   See definitions/places.md."
where
  | base "The base local variable." : Local
  | projection "The list of projection elements."
      : List ProjElem
  deriving Repr, BEq, Hashable
