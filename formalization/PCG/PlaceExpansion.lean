import Core.Dsl.DefEnum
import MIR.Place
import MIR.Ty
import PCG.RequiredGuide

defEnum PlaceExpansion {D}
    (.text "xp", .text "PlaceExpansion")
  "Place Expansions"
  (doc! "A place expansion \
    $_xp_ ∈ _PlaceExpansion_ _D_$ \
    describes the projections produced by expanding a place: \
    either a set of struct/tuple fields, a deref, or a \
    guided expansion (enum downcast, array index, or \
    subslice). Each expanded child carries a per-child \
    payload drawn from a parameter set $#D$. The \
    {Doc.math (.doc (.code "fields"))} variant carries the \
    children as a list of \
    {Doc.math (.text "(field, type, payload)")} triples, \
    kept in ascending field-index order so that two \
    structurally-equal expansions have identical \
    representations.") long
where
  | fields (children : List (FieldIdx × Ty × D))
    "A struct/tuple field expansion."
  | deref (d : D)
    "A dereference."
  | guided (guide : RequiredGuide D)
    "A guided expansion."
  deriving Repr
