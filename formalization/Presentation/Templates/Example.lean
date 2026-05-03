import Presentation
import Core.Dsl.RegisterPresentation
import MIR

/-! # Example template presentation

A small template presentation embedding the `Place` definition.
Exercises the closure logic end-to-end: `Place` references
`Local` and `ProjElem`; `ProjElem`'s variants in turn reference
`FieldIdx`, `Ty`, `VariantIdx`, and several `Ty` cases recurse
into other registered types — every transitively-referenced
registered definition that is *not* explicitly listed in
`elems` lands in the rendered Appendix.

The template is registered into the global presentation
registry; the presentation exporter writes
`generated/place.pdf` next to the full PDF on every export. -/

def placeTemplate : Presentation := {
  filename := "place"
  title    := "Places"
  -- Disabling `ENUM_TYPES` hides every `downcast` variant
  -- and every `.downcast` match arm reachable from this
  -- template's appendix, so the focused PDF doesn't have to
  -- explain enum projections.
  disabledFeatures := [.enumTypes]
  elems    := [
    .doc (doc!
      "A focused look at the `Place` definition and its \
       transitive dependencies. Definitions referenced by \
       `Place` but not embedded directly here are rendered \
       in the Appendix below."),
    .defRef "Place"
  ]
}

registerPresentation placeTemplate
