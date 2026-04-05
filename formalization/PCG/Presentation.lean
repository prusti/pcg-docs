import PCG.Capability.Order
import MIR
import Core.Dsl.Types.OrderDef
import Core.Registry

/-- Build a lookup function that maps enum constructor names
    to their LaTeX display form, using displayName from all
    registered enums. -/
private def mkCtorDisplay
    (enums : List RegisteredEnum)
    : String → Option String :=
  fun ctorName =>
    let found := enums.flatMap fun e =>
      e.enumDef.variants.filterMap fun v =>
        if v.name.name == ctorName then
          some v.displayLatexMath
        else none
    found.head?

/-- Get the module name (last component of a Lean name). -/
private def moduleName (n : Lean.Name) : String :=
  match n with
  | .str _ s => s
  | _ => "Unknown"

/-- Build the LaTeX for a single module (subsection) within
    a crate. -/
private def moduleLatex
    (modName : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option String)
    (allVariants : List VariantDef)
    : String :=
  let lb := "{"
  let rb := "}"
  let header := s!"\\subsection{lb}{modName}{rb}\n"
  let structParts := structs.map fun s =>
    s!"{s.structDef.formalDefLatex}\n"
  let enumParts := enums.flatMap fun e =>
    let def_ := s!"{e.enumDef.formalDefLatex}\n"
    let orderParts := orders.filter
      (·.enumName == e.enumDef.name.name) |>.map fun o =>
        s!"\\subsubsection{lb}Ordering{rb}\n\
           {o.orderDef.hasseDiagram e.enumDef
             |>.toLaTeX}\n"
    def_ :: orderParts
  let fnParts := fns.map fun f =>
    s!"{f.fnDef.formalDefLatex ctorDisplay
         allVariants}\n"
  let propParts := properties.map fun p =>
    s!"{p.propertyDef.formalDefLatex ctorDisplay
         allVariants}\n"
  header ++
    "\n".intercalate
      (structParts ++ enumParts ++ fnParts ++
       propParts)

/-- Build the presentation sections for a single crate
    prefix, grouped by module (subsection). -/
private def crateLatex
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option String)
    (allVariants : List VariantDef)
    : String :=
  let crateEnums := enums.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateStructs := structs.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateOrders := orders.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateFns := fns.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateProps := properties.filter
    (·.leanModule.getRoot.toString == prefix_)
  -- Collect unique module names (preserving order)
  let allModNames := (
    crateStructs.map (moduleName ·.leanModule) ++
    crateEnums.map (moduleName ·.leanModule) ++
    crateFns.map (moduleName ·.leanModule) ++
    crateProps.map (moduleName ·.leanModule)
  ).foldl (init := [])
    fun acc m =>
      if acc.contains m then acc else acc ++ [m]
  let lb := "{"
  let rb := "}"
  let sectionHeader :=
    s!"\\section{lb}{prefix_}{rb}\n"
  let modules := allModNames.map fun mn =>
    let modEnums := crateEnums.filter
      (moduleName ·.leanModule == mn)
    let modStructs := crateStructs.filter
      (moduleName ·.leanModule == mn)
    let modEnumNames := modEnums.map
      (·.enumDef.name.name)
    let modOrders := crateOrders.filter
      fun o => modEnumNames.contains o.enumName
    let modFns := crateFns.filter
      (moduleName ·.leanModule == mn)
    let modProps := crateProps.filter
      (moduleName ·.leanModule == mn)
    moduleLatex mn modEnums modStructs modOrders
      modFns modProps ctorDisplay allVariants
  sectionHeader ++ "\n".intercalate modules

/-- Build the full presentation LaTeX body from all
    registered definitions. -/
def buildPresentationLatex
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : String :=
  let prefixes := (
    enums.map (·.leanModule.getRoot.toString) ++
    structs.map (·.leanModule.getRoot.toString) ++
    fns.map (·.leanModule.getRoot.toString) ++
    properties.map (·.leanModule.getRoot.toString)
  ).foldl (init := [])
    fun acc p =>
      if acc.contains p then acc else acc ++ [p]
  let ctorDisplay := mkCtorDisplay enums
  let allVariants := enums.flatMap
    (·.enumDef.variants)
  let body := prefixes.map
    fun p => crateLatex p enums structs orders fns
      properties ctorDisplay allVariants
  "\n".intercalate body

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String :=
  ["tikz", "amsmath", "amssymb", "amsthm",
   "algorithm", "algpseudocode"]

/-- Extra LaTeX preamble (theorem definitions, etc). -/
def latexPreamble : String :=
  "\\newtheorem{definition}{Definition}\n"
