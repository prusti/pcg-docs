import PCG.Capability.Order
import MIR.Ty
import Shared.OrderDef
import Shared.Registry

/-- Render an enum definition section: its long (descriptive) and
    short (formal grammar) forms. -/
private def enumSection (e : EnumDef) : Doc :=
  .seq [e.longDef, .line, .line, e.shortDef]

/-- Join document fragments with double line breaks. -/
private def sections (ds : List Doc) : Doc :=
  Doc.intercalate (.seq [.line, .line]) ds

/-- Build the presentation sections for a single crate prefix
    (e.g. `"PCG"` or `"MIR"`), including all registered enums,
    structs, and orderings. -/
private def crateSection
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    : List Doc :=
  let crateEnums := enums.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateStructs := structs.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateOrders := orders.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateFns := fns.filter
    (·.leanModule.getRoot.toString == prefix_)
  let header := [Doc.bold (.text prefix_)]
  let structDocs := crateStructs.map fun s =>
    .seq [ .bold (.text s.structDef.name)
         , .line, .line
         , .text s.structDef.doc ]
  let enumDocs := crateEnums.flatMap fun e =>
    let base :=
      [ .bold (.text e.enumDef.name)
      , enumSection e.enumDef ]
    let orderDocs := crateOrders.filter
      (·.enumName == e.enumDef.name)
      |>.map fun o =>
        .seq [ .bold (.text "Ordering")
             , .line, .line
             , o.orderDef.hasseDiagram e.enumDef ]
    base ++ orderDocs
  let fnDocs := crateFns.map fun f =>
    .seq [ .bold (.text f.fnDef.name)
         , .line, .line
         , f.fnDef.algorithmDoc ]
  header ++ structDocs ++ enumDocs ++ fnDocs

/-- Build the full presentation from all registered definitions.
    Grouped by crate prefix (PCG, MIR). -/
def buildPresentation
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    : Doc :=
  let prefixes := (
    enums.map (·.leanModule.getRoot.toString) ++
    structs.map (·.leanModule.getRoot.toString) ++
    fns.map (·.leanModule.getRoot.toString)
  ).foldl (init := [])
    fun acc p => if acc.contains p then acc else acc ++ [p]
  let allSections := prefixes.flatMap
    fun p => crateSection p enums structs orders fns
  sections allSections

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String := ["tikz", "amsmath"]
