import Presentation
import Core.Dsl.RegisterPresentation
import Core.Doc.PresInterp
import MIR

def template : Presentation := {
  filename := "louis"
  title    := "Louis"
  disabledFeatures := [.enumTypes, .refTypes]
  elems    := presBody!
    "

The PCG uses the `InitTree` data structure to track partial move-outs of places.

[[InitTree]]

A focused look at the `Place` definition and its transitive dependencies. Definitions referenced by `Place` but not embedded directly here are rendered in the Appendix below.

[[Place]]"
}
registerPresentation template
