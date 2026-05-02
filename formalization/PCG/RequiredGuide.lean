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
  subscript
where
  | downcast (variant : VariantIdx) (data : D)
    "An enum downcast."
  | constantIndex (offset : Nat) (data : D)
    "A constant array index."
    (mathdoc! "{(MathDoc.doc (.code "constIdx "))}n D")
  | index (loc : Local) (data : D)
    "A variable array index."
  | subslice (from_ : Nat) (to_ : Nat) (fromEnd : Bool)
      (data : D)
    "An array subslice."
    (mathdoc! "{(MathDoc.doc (.code "subslice "))}n..n B D")
