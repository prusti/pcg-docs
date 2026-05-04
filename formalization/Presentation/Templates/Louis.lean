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

The PCG model distinguishes places as being either _owned_ or _borrowed_.
Intuitively, _owned_ places are those that do not dereference any
reference-typed value. Formally, this classification is determined as follows:

[[isOwned]]

In this project, you will be formalising properties about how PCG tracks the
_owned_ places in a program, in particular

The PCG tracks what places have been moved out at particular program points by
associating them with an `InitialisationState`, defined as follows:

[[InitialisationState]]


The PCG uses the `InitTree` data structure to track partial move-outs of places.

[[InitTree]]

A focused look at the `Place` definition and its transitive dependencies. Definitions referenced by `Place` but not embedded directly here are rendered in the Appendix below.

[[Place]]"
}
registerPresentation template
