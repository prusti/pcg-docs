import Core.Dsl.DefEnum
import MIR.Place
import MIR.Ty
import PCG.RequiredGuide

defEnum PlaceExpansion {D}
    (.text "xp", .text "PlaceExpansion")
  "Place Expansions"
  (doc! "A place expansion \
    {.math (.seq [(.text "xp"), .sym .setContains, (.text "PlaceExpansion"), .sym .space, .raw "D"])} \
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
    representations.")
where
  | fields (children : List (FieldIdx × Ty × D))
    "A struct/tuple field expansion."
    (.doc (.code "fields "),
     #children (.text "fs"))
  | deref (data : D)
    "A dereference."
  | guided (guide : RequiredGuide D)
    "A guided expansion."
  deriving Repr
