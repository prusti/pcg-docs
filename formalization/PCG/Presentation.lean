import PCG.Capability.Order
import MIR.Ty
import Shared.OrderDef
import Shared.Registry

/-- Build a lookup function that maps enum constructor names
    to their LaTeX display form, using displayName from all
    registered enums. -/
private def mkCtorDisplay
    (enums : List RegisteredEnum)
    : String → Option String :=
  fun ctorName =>
    let found := enums.flatMap fun e =>
      e.enumDef.variants.filterMap fun v =>
        if v.name == ctorName then
          some v.displayLatexMath
        else none
    found.head?

/-- Build the presentation sections for a single crate prefix
    as raw LaTeX strings. -/
private def crateLatex
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
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
  let sectionHeader := s!"\\section{lb}{prefix_}{rb}\n"
  let structParts := crateStructs.map fun s =>
    s!"\\subsection{lb}{s.structDef.name}{rb}\n\
       {s.structDef.formalDefLatex}\n"
  let enumParts := crateEnums.flatMap fun e =>
    let def_ :=
      s!"\\subsection{lb}{e.enumDef.name}{rb}\n\
         {e.enumDef.formalDefLatex}\n"
    let orderParts := crateOrders.filter
      (·.enumName == e.enumDef.name) |>.map fun o =>
        let lb := "{"
        let rb := "}"
        s!"\\subsubsection{lb}Ordering{rb}\n\
           {o.orderDef.hasseDiagram e.enumDef
             |>.toLaTeX}\n"
    def_ :: orderParts
  let fnParts := crateFns.map fun f =>
    s!"\\subsection{lb}{f.fnDef.name}{rb}\n\
       {f.fnDef.formalDefLatex ctorDisplay
         allVariants}\n"
  sectionHeader ++
    "\n".intercalate
      (structParts ++ enumParts ++ fnParts)
  where lb := "{" ; rb := "}"

/-- Build the full presentation LaTeX body from all
    registered definitions. -/
def buildPresentationLatex
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    : String :=
  let prefixes := (
    enums.map (·.leanModule.getRoot.toString) ++
    structs.map (·.leanModule.getRoot.toString) ++
    fns.map (·.leanModule.getRoot.toString)
  ).foldl (init := [])
    fun acc p =>
      if acc.contains p then acc else acc ++ [p]
  let ctorDisplay := mkCtorDisplay enums
  let allVariants := enums.flatMap
    (·.enumDef.variants)
  let body := prefixes.map
    fun p => crateLatex p enums structs orders fns
      ctorDisplay allVariants
  "\n".intercalate body

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String :=
  ["tikz", "amsmath", "amssymb", "amsthm",
   "algorithm", "algpseudocode"]

/-- Extra LaTeX preamble (theorem definitions, etc). -/
def latexPreamble : String :=
  "\\newtheorem{definition}{Definition}\n"
