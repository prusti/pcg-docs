import PCG.Capability.Order
import MIR
import Core.Dsl.Types.OrderDef
import Core.Registry

/-- Build a lookup function that maps enum constructor
    names to their LaTeX display form. -/
private def mkCtorDisplay
    (enums : List RegisteredEnum)
    : String → Option LatexMath :=
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

/-- Build the LaTeX for a single module subsection. -/
private def moduleLatex
    (modName : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option LatexMath)
    (allVariants : List VariantDef)
    (knownFns : String → Bool)
    (knownCtors : String → Bool)
    : Latex :=
  let header := Latex.subsection (.raw modName)
  let structParts := structs.map fun s =>
    Latex.seq [s.structDef.formalDefLatex,
               .newline, .newline]
  let enumParts := enums.flatMap fun e =>
    let def_ := Latex.seq
      [e.enumDef.formalDefLatex, .newline, .newline]
    let orderParts := orders.filter
      (·.enumName == e.enumDef.name.name) |>.map
        fun o =>
          Latex.seq [
            Latex.subsubsection (.raw "Ordering"),
            .newline,
            (o.orderDef.hasseDiagram e.enumDef).toLatex,
            .newline, .newline ]
    def_ :: orderParts
  let fnParts := fns.map fun f =>
    Latex.seq [f.fnDef.formalDefLatex ctorDisplay
                 allVariants (knownFns := knownFns)
                 (knownCtors := knownCtors),
               .newline, .newline]
  let propParts := properties.map fun p =>
    Latex.seq [p.propertyDef.formalDefLatex ctorDisplay
                 allVariants (knownFns := knownFns)
                 (knownCtors := knownCtors),
               .newline, .newline]
  .seq ([header, .newline] ++
    structParts ++ enumParts ++ fnParts ++ propParts)

/-- Build the LaTeX sections for a single crate prefix,
    grouped by module. -/
private def crateLatex
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option LatexMath)
    (allVariants : List VariantDef)
    (knownFns : String → Bool)
    (knownCtors : String → Bool)
    : Latex :=
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
  let allModNames := (
    crateStructs.map (moduleName ·.leanModule) ++
    crateEnums.map (moduleName ·.leanModule) ++
    crateFns.map (moduleName ·.leanModule) ++
    crateProps.map (moduleName ·.leanModule)
  ).foldl (init := [])
    fun acc m =>
      if acc.contains m then acc else acc ++ [m]
  let sectionHeader := Latex.section (.raw prefix_)
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
      modFns modProps ctorDisplay allVariants knownFns
      knownCtors
  .seq ([sectionHeader, .newline] ++ modules)

/-- Build the full presentation LaTeX body. -/
def buildPresentationLatex
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : Latex :=
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
  let fnNameSet : List String :=
    fns.map (·.fnDef.name) ++
      properties.map (·.propertyDef.fnDef.name)
  let knownFns : String → Bool :=
    fun n => fnNameSet.contains n
  let ctorNameSet : List String :=
    allVariants.map (·.name.name)
  -- Accept either short (`int`) or qualified
  -- (`Value.int`) ctor references.
  let knownCtors : String → Bool :=
    fun n =>
      let shortName := (n.splitOn ".").getLast?.getD n
      ctorNameSet.contains shortName
  let body := prefixes.map
    fun p => crateLatex p enums structs orders fns
      properties ctorDisplay allVariants knownFns
      knownCtors
  .seq body

/-- LaTeX packages needed by the presentation. -/
def latexPackages : List String :=
  ["tikz", "amsmath", "amssymb", "amsthm",
   "algorithm", "algpseudocode", "hyperref", "xcolor"]

/-- Extra LaTeX preamble (theorem definitions, etc). -/
def latexPreamble : Latex :=
  .seq [
    .raw "\\newtheorem{definition}{Definition}\n",
    -- Number algorithms and definitions per subsection, so
    -- an algorithm/definition in subsection 3.8 is rendered
    -- as "Algorithm 3.8.1", "Definition 3.8.1", etc.
    .raw "\\numberwithin{algorithm}{subsection}\n",
    .raw "\\numberwithin{definition}{subsection}\n",
    .raw "\\usepackage[normalem]{ulem}\n",
    -- Redefine `\dashuline` so hyperlinks get a denser,
    -- grey dashed underline instead of ulem's default
    -- (wider, black) dashes. The definition mirrors
    -- ulem's own (including `\leavevmode`, ULdepth
    -- handling, and the protected robust wrapper) so
    -- `\dashuline` keeps working inside fragile
    -- contexts like `\hyperref`/`\hyperlink`.
    .raw ("\\makeatletter\n"
      ++ "\\UL@protected\\def\\dashuline{"
      ++ "\\leavevmode \\bgroup\n"
      ++ "  \\UL@setULdepth\n"
      ++ "  \\ifx\\UL@on\\UL@onin "
      ++ "\\advance\\ULdepth2\\p@\\fi\n"
      ++ "  \\markoverwith{\\kern.04em\n"
      ++ "    \\textcolor{gray}{\\vtop{"
      ++ "\\kern\\ULdepth \\hrule width .08em}}%\n"
      ++ "    \\kern.04em}\\ULon}\n"
      ++ "\\makeatother\n"),
    .raw ("\\hypersetup{colorlinks=false, "
      ++ "pdfborder={0 0 0}}\n")
  ]
