import PCG.Capability.Order
import Shared.OrderDef

/-- The presentation document for the PCG formalization. -/
def presentation : Doc :=
  let capDef := Capability.enumDef
  let capOrder := Capability.orderDef
  .seq
    [ .bold (.text "Capability")
    , .line, .line
    , capDef.longDef
    , .line, .line
    , capDef.shortDef
    , .line, .line
    , .bold (.text "Ordering")
    , .line, .line
    , capOrder.hasseDiagram capDef
    ]

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String := ["tikz"]
