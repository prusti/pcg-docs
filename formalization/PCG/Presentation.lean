import PCG.Capability.Order
import MIR.Region
import Shared.OrderDef

/-- Render an enum definition section: its long (descriptive) and
    short (formal grammar) forms. -/
private def enumSection (e : EnumDef) : Doc :=
  .seq [e.longDef, .line, .line, e.shortDef]

/-- Join document fragments with double line breaks. -/
private def sections (ds : List Doc) : Doc :=
  Doc.intercalate (.seq [.line, .line]) ds

/-- The presentation document for the PCG formalization.
    Organised into a PCG section (capability + ordering) and an
    MIR section (region). -/
def presentation : Doc :=
  let capDef := Capability.enumDef
  let capOrder := Capability.orderDef
  let regDef := Region.enumDef
  sections
    [ .bold (.text "PCG")
    , .bold (.text capDef.name)
    , enumSection capDef
    , .bold (.text "Ordering")
    , capOrder.hasseDiagram capDef
    , .bold (.text "MIR")
    , .bold (.text regDef.name)
    , enumSection regDef
    ]

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String := ["tikz"]
