import Core.Dsl.DefEnum
import MIR.Place

defEnum RequiredGuide {D}
    (.doc (.plain "rg"), .doc (.plain "RequiredGuide"))
  "Required Guides"
  (.seq [
    .plain "A required guide ",
    Doc.defMath (.doc (.plain "rg"))
      (.doc (.plain "RequiredGuide")) ["D"],
    .plain " selects a non-default expansion variant: an enum \
     downcast, a constant array index, a variable array \
     index, or a subslice. Each variant carries a per-child \
     payload drawn from a parameter set ",
    .math (.doc (.plain "D")),
    .plain "."])
where
  | downcast (variant : VariantIdx) (data : D)
    "An enum downcast."
  | constantIndex (offset : Nat) (data : D)
    "A constant array index."
    (.doc (.code "constIdx "), #offset (.raw "n"),
     .doc (.plain " "), #data (.doc (.plain "D")))
  | index (loc : Local) (data : D)
    "A variable array index."
  | subslice (from_ : Nat) (to_ : Nat) (fromEnd : Bool)
      (data : D)
    "An array subslice."
    (.doc (.code "subslice "), #from_ (.raw "n"),
     .doc (.plain ".."), #to_ (.raw "n"),
     .doc (.plain " "), #fromEnd (.doc (.plain "B")),
     .doc (.plain " "), #data (.doc (.plain "D")))
