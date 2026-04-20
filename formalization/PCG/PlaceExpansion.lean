import Core.Dsl.DefEnum
import MIR.Place
import MIR.Ty
import PCG.RequiredGuide

defEnum PlaceExpansion {D}
    (.doc (.plain "xp"), .doc (.plain "PlaceExpansion"))
  "Place Expansions"
  (.seq [
    .plain "A place expansion ",
    Doc.defMath (.doc (.plain "xp"))
      (.doc (.plain "PlaceExpansion")),
    .plain " describes the projections produced by expanding \
     a place: either a set of struct/tuple fields, a deref, \
     or a guided expansion (enum downcast, array index, or \
     subslice). Each expanded child carries a per-child \
     payload drawn from a parameter set ",
    .math (.doc (.plain "D")),
    .plain ". The ",
    .math (.doc (.code "fields")),
    .plain " variant carries the children as a list of ",
    .math (.doc (.plain "(field, type, payload)")),
    .plain " triples, kept in ascending field-index order so \
     that two structurally-equal expansions have identical \
     representations."])
where
  | fields (children : List (FieldIdx × Ty × D))
    "A struct/tuple field expansion."
    (.doc (.code "fields "),
     #children (.doc (.plain "fs")))
  | deref (data : D)
    "A dereference."
  | guided (guide : RequiredGuide D)
    "A guided expansion."
  deriving Repr
