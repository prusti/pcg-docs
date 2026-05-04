import Presentation
import Core.Dsl.RegisterPresentation
import Core.Doc.PresInterp
import MIR

def template : Presentation := {
  filename := "louis"
  title    := "Formalising PCG's Tracking of Owned Places"
  disabledFeatures := [.enumTypes, .refTypes, .aliasTypes]
  elems    := presBody!
    "

# Background

## Owned vs Borrowed Places

The PCG model distinguishes places as being either _owned_ or _borrowed_.
Intuitively, _owned_ places are those that do not dereference any
reference-typed value. Formally, this classification is determined as follows:

[[isOwned]]

For this project, the focus is on the handling of owned places only. The PCG
tracks what places have been moved out at particular program points by
associating them with an `InitialisationState`, defined as follows:

[[InitialisationState]]

For now you can ignore the \"Shallowly Initialized\" case. The Deep (__D__)
capability corresponds to the PCG's Exclusive (__E__) capability, and Uninitialised
(__U__) corresponds to __W__.

The PCG uses the `InitTree` data structure to track partial move-outs of places.

[[InitTree]]

A focused look at the `Place` definition and its transitive dependencies. Definitions referenced by `Place` but not embedded directly here are rendered in the Appendix below.

[[Place]]"
}
registerPresentation template
