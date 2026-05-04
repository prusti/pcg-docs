import Core.Dsl.DefEnum
import MIR.Place

defEnum RequiredGuide {D}
    (.text "rg", .text "RequiredGuide")
  "Required Guides"
  (doc! "A required guide \
    $_rg_ ∈ _RequiredGuide_ _D_$ \
    selects a non-default expansion variant: an enum \
    downcast, a constant array index, a variable array \
    index, or a subslice. Each variant carries a per-child \
    payload drawn from a parameter set $#D$.")
  long subscript
where
  | [feature ENUM_TYPES] downcast (variant : VariantIdx) (data : D)
    "An enum downcast."
  | constantIndex (n : Nat) (d : D)
    "A constant array index."
    (mathdoc! "_constIdx_ {n} {d}")
  | index (loc : Local) (data : D)
    "A variable array index."
  | subslice (n : Nat) (n' : Nat) (fromEnd : Bool)
      (d : D)
    "An array subslice."
    (mathdoc! "_subslice_ [{n}..{n'}] {fromEnd} {d}")
