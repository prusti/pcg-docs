import PCG.Capability.Order
import MIR
import Core.Dsl.Types.OrderDef
import Core.Registry

/-- Build a lookup function that maps enum constructor
    names to their `MathDoc` display form. -/
private def mkCtorDisplay
    (enums : List RegisteredEnum)
    : String → Option MathDoc :=
  fun ctorName =>
    let found := enums.flatMap fun e =>
      e.enumDef.variants.filterMap fun v =>
        if v.name.name == ctorName then
          some v.displayMathDoc
        else none
    found.head?

/-- Get the module name (last component of a Lean name). -/
private def moduleName (n : Lean.Name) : String :=
  match n with
  | .str _ s => s
  | _ => "Unknown"

/-- Number of dotted components in a module name. -/
private def modDepth (n : Lean.Name) : Nat :=
  n.components.length

/-- Whether `m` is an immediate child module of `p`. -/
private def isChildOf (p m : Lean.Name) : Bool :=
  let pComps := p.components
  let mComps := m.components
  mComps.length == pComps.length + 1 &&
    pComps == mComps.take pComps.length

/-- Subsubsection title for a nested module: combine the
    module's own last component with its parent's last
    component (e.g. `OpSem.Expressions.Place` →
    `"Place Expressions"`). -/
private def subsubTitle (n : Lean.Name) : String :=
  let parent := match n.components.dropLast.getLast? with
    | some p => moduleName p
    | none => ""
  s!"{moduleName n} {parent}"

/-- Build the LaTeX body (no header) for a single module:
    its descriptions, struct, enum, function, and property
    definitions in order, each followed by two newlines. -/
private def moduleBodyLatex
    (descrs : List RegisteredDescr)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option MathDoc)
    (allVariants : List VariantDef)
    (knownFns : String → Bool)
    (resolveCtor : String → Option String)
    (knownTypes : String → Bool)
    (precondShortUsage :
      String → List Doc → Option Doc)
    : Latex :=
  let descrParts := descrs.map fun d =>
    Latex.seq [d.doc.toLatex, .newline, .newline]
  let structParts := structs.map fun s =>
    Latex.seq [s.structDef.formalDefLatex knownTypes,
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
                 (resolveCtor := resolveCtor)
                 (knownTypes := knownTypes)
                 (precondShortUsage := precondShortUsage),
               .newline, .newline]
  let propParts := properties.map fun p =>
    Latex.seq [p.propertyDef.formalDefLatex ctorDisplay
                 allVariants (knownFns := knownFns)
                 (resolveCtor := resolveCtor)
                 (knownTypes := knownTypes)
                 (precondShortUsage := precondShortUsage),
               .newline, .newline]
  .seq (descrParts ++ structParts ++ enumParts
    ++ fnParts ++ propParts)

/-- Build the LaTeX sections for a single crate prefix,
    grouped by module. -/
private def crateLatex
    (prefix_ : String)
    (descrs : List RegisteredDescr)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (ctorDisplay : String → Option MathDoc)
    (allVariants : List VariantDef)
    (knownFns : String → Bool)
    (resolveCtor : String → Option String)
    (knownTypes : String → Bool)
    (precondShortUsage :
      String → List Doc → Option Doc)
    : Latex :=
  let crateDescrs := descrs.filter
    (·.leanModule.getRoot.toString == prefix_)
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
  -- Collect all module `Lean.Name`s in registration order,
  -- de-duplicated. We keep the full `Lean.Name` so the
  -- hierarchy (e.g. `OpSem.Expressions.Place` nested under
  -- `OpSem.Expressions`) is recoverable.
  let allMods : List Lean.Name := (
    crateDescrs.map (·.leanModule) ++
    crateStructs.map (·.leanModule) ++
    crateEnums.map (·.leanModule) ++
    crateFns.map (·.leanModule) ++
    crateProps.map (·.leanModule)
  ).foldl (init := [])
    fun acc m =>
      if acc.contains m then acc else acc ++ [m]
  -- Subsections are modules directly under the crate
  -- (depth 2), e.g. `OpSem.Expressions`. Anything deeper
  -- becomes a subsubsection within its depth-2 ancestor.
  let topMods := allMods.filter fun m => modDepth m == 2
  let buildBody := fun (mod : Lean.Name) =>
    let modDescrs := crateDescrs.filter
      (·.leanModule == mod)
    let modEnums := crateEnums.filter
      (·.leanModule == mod)
    let modStructs := crateStructs.filter
      (·.leanModule == mod)
    let modEnumNames := modEnums.map
      (·.enumDef.name.name)
    let modOrders := crateOrders.filter
      fun o => modEnumNames.contains o.enumName
    let modFns := crateFns.filter
      (·.leanModule == mod)
    let modProps := crateProps.filter
      (·.leanModule == mod)
    moduleBodyLatex modDescrs modEnums modStructs
      modOrders modFns modProps ctorDisplay allVariants
      knownFns resolveCtor knownTypes precondShortUsage
  let sectionHeader := Latex.section (.raw prefix_)
  let modules := topMods.map fun topMod =>
    let header :=
      Latex.subsection (.raw (moduleName topMod))
    let body := buildBody topMod
    -- Nested submodules whose immediate parent is this
    -- top-level module become subsubsections.
    let nestedMods := allMods.filter (isChildOf topMod)
    let nestedParts := nestedMods.map fun nm =>
      Latex.seq [
        Latex.subsubsection (.raw (subsubTitle nm)),
        .newline,
        buildBody nm ]
    .seq ([header, .newline, body] ++ nestedParts)
  .seq ([sectionHeader, .newline] ++ modules)

/-- Build the full presentation LaTeX body. -/
def buildPresentationLatex
    (descrs : List RegisteredDescr)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (orders : List RegisteredOrder)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : Latex :=
  let prefixes := (
    descrs.map (·.leanModule.getRoot.toString) ++
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
  -- Build a table of `(shortName, qualifiedName)` pairs
  -- where the qualified name is
  -- `EnumName.variantName`. This is used to resolve
  -- constructor references to their fully-qualified
  -- anchors, so that variants with the same short name
  -- in different enums (e.g. `Value.tuple` and
  -- `ValueExpr.tuple`) can be linked independently.
  let ctorPairs : List (String × String) :=
    enums.flatMap fun e =>
      e.enumDef.variants.map fun v =>
        (v.name.name,
         s!"{e.enumDef.name.name}.{v.name.name}")
  -- Resolve a constructor reference to its
  -- fully-qualified name. Accepts either short (`int`)
  -- or already-qualified (`Value.int`) forms. Returns
  -- `none` if the name does not resolve to any known
  -- variant.
  let resolveCtor : String → Option String :=
    fun n =>
      if n.contains '.' then
        if ctorPairs.any (·.2 == n) then some n
        else none
      else
        (ctorPairs.find? (·.1 == n)).map (·.2)
  let typeNameSet : List String :=
    enums.map (·.enumDef.name.name) ++
      structs.map (·.structDef.name)
  let knownTypes : String → Bool :=
    fun n => typeNameSet.contains n
  let precondShortUsage :
      String → List Doc → Option Doc :=
    fun nm args =>
      (properties.find?
          (·.propertyDef.fnDef.name == nm)).map
        fun rp => rp.propertyDef.doc args
  let sections := prefixes.map
    fun p => crateLatex p descrs enums structs orders
      fns properties ctorDisplay allVariants knownFns
      resolveCtor knownTypes precondShortUsage
  .seq ([.tableofcontents, .newpage] ++ sections)

/-- LaTeX packages needed by the presentation.

    `placeins` provides `\FloatBarrier`, which the
    `section`/`subsection` helpers emit before each heading
    so that all content of a (sub)section appears before the
    next (sub)section begins. -/
def latexPackages : List String :=
  ["tikz", "amsmath", "amssymb", "amsthm",
   "algorithm", "algpseudocode", "hyperref", "xcolor",
   "placeins"]

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
