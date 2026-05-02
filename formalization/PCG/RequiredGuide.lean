import Core.Dsl.DefEnum
import MIR.Place

defEnum RequiredGuide {D}
    (.text "rg", .text "RequiredGuide")
  "Required Guides"
  (doc! "A required guide \
    {.math (.seq [(.text "rg"), .sym .setContains, (.text "RequiredGuide"), .sym .space, .raw "D"])} \
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
    (.doc (.code "constIdx "), #offset (.raw "n"),
     .text " ", #data (.text "D"))
  | index (loc : Local) (data : D)
    "A variable array index."
  | subslice (from_ : Nat) (to_ : Nat) (fromEnd : Bool)
      (data : D)
    "An array subslice."
    (.doc (.code "subslice "), #from_ (.raw "n"),
     .text "..", #to_ (.raw "n"),
     .text " ", #fromEnd (.text "B"),
     .text " ", #data (.text "D"))
