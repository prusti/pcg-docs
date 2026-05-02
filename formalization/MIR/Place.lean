import MIR.Ty
import Core.Dsl.DefAlias

defStruct Local (.raw "l", .raw "L")
  "Locals"
  (doc! "A local $_l_ ∈ _L_$ is a \
    variable in the MIR, identified by index.")
  constructor "LocalIdx"
where
  | index "The local variable index." : Nat
  deriving DecidableEq, BEq, Repr, Hashable

defStruct FieldIdx (.raw "f", .raw "F")
  "Field Indices"
  (.plain "A field index within a struct or tuple.")
  constructor "FieldIdx"
where
  | index "The field index." : Nat

defStruct VariantIdx (.raw "V",
    .text "VariantIdx")
  "Variant Indices"
  (.plain "A variant index within an enum.")
  constructor "VariantIdx"
where
  | index "The variant index." : Nat

defEnum ProjElem (.raw "π", .raw "Π")
  "Projection Elements"
  (doc! "A projection element applied to a place. See `definitions/places.md`.")
where
  | deref
    "Dereference a pointer or reference."
    (.doc (.code "*"))
  | field (idx : FieldIdx) (ty : Ty)
    "Access a field by index."
    (.text ".",
     #idx,
     .text " : ",
     #ty)
  | index (idx : Local)
    "Index into an array or slice."
    (.sym .lbracket,
     #idx,
     .sym .rbracket)
  | downcast (variant : VariantIdx)
    "Downcast an enum to a specific variant."
    (.text "@",
     #variant)
  deriving Repr, BEq, Hashable

defStruct Place (.raw "p", .raw "P")
  "Places"
  (doc! "A place in the MIR: a local with a projection. See `definitions/places.md`.")
where
  | «local» "The local variable." : Local
  | projection "The list of projection elements."
      : List ProjElem
  deriving Repr, BEq, Hashable

defAlias RETURN = Place⟨Local⟨0⟩, []⟩
