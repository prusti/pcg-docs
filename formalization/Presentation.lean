import PCG.BorrowChecker
import PCG.Capability.Order
import PCG.InitialisationState.Order
import PCG.LifetimeProjection
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

namespace Registry

/-- Keep only the definitions registered from `mod`.

    Orders are kept when their enum belongs to `mod`, since
    `RegisteredOrder` is attached to an enum name rather than
    a module. -/
def restrictToModule
    (reg : Registry) (mod : Lean.Name) : Registry :=
  let modEnums := reg.enums.filter (·.leanModule == mod)
  let modEnumNames := modEnums.map (·.enumDef.name.name)
  { descrs := reg.descrs.filter (·.leanModule == mod)
    enums := modEnums
    structs := reg.structs.filter (·.leanModule == mod)
    orders := reg.orders.filter
      fun o => modEnumNames.contains o.enumName
    fns := reg.fns.filter (·.leanModule == mod)
    properties := reg.properties.filter
      (·.leanModule == mod) }

/-- Keep only the definitions whose module's root crate
    prefix equals `crate`. -/
def restrictToCrate
    (reg : Registry) (crate : String) : Registry :=
  let p (m : Lean.Name) : Bool :=
    m.getRoot.toString == crate
  { descrs := reg.descrs.filter (fun d => p d.leanModule)
    enums := reg.enums.filter (fun e => p e.leanModule)
    structs := reg.structs.filter (fun s => p s.leanModule)
    orders := reg.orders
    fns := reg.fns.filter (fun f => p f.leanModule)
    properties := reg.properties.filter
      (fun q => p q.leanModule) }

/-- Union of every module name that appears in the registry
    (de-duplicated, preserving registration order). -/
def moduleNames (reg : Registry) : List Lean.Name :=
  (reg.descrs.map (·.leanModule)
    ++ reg.structs.map (·.leanModule)
    ++ reg.enums.map (·.leanModule)
    ++ reg.fns.map (·.leanModule)
    ++ reg.properties.map (·.leanModule)
  ).foldl (init := [])
    fun acc m =>
      if acc.contains m then acc else acc ++ [m]

/-- Union of every crate prefix appearing in the registry. -/
def cratePrefixes (reg : Registry) : List String :=
  (reg.descrs.map (·.leanModule.getRoot.toString)
    ++ reg.enums.map (·.leanModule.getRoot.toString)
    ++ reg.structs.map (·.leanModule.getRoot.toString)
    ++ reg.fns.map (·.leanModule.getRoot.toString)
    ++ reg.properties.map (·.leanModule.getRoot.toString)
  ).foldl (init := [])
    fun acc p =>
      if acc.contains p then acc else acc ++ [p]

end Registry

/-- Build the LaTeX body (no header) for a single module:
    its descriptions, struct, enum, function, and property
    definitions in order, each followed by two newlines. -/
private def moduleBodyLatex
    (reg : Registry) (ctx : RenderCtx) : Latex :=
  let descrParts := reg.descrs.map fun d =>
    Latex.seq [d.doc.toLatex, .newline, .newline]
  let structParts := reg.structs.map fun s =>
    Latex.seq [s.structDef.formalDefLatex ctx.knownTypes,
               .newline, .newline]
  let enumParts := reg.enums.flatMap fun e =>
    let def_ := Latex.seq
      [e.enumDef.formalDefLatex, .newline, .newline]
    let orderParts := reg.orders.filter
      (·.enumName == e.enumDef.name.name) |>.map
        fun o =>
          Latex.seq [
            Latex.subsubsection (.raw "Ordering"),
            .newline,
            o.orderDef.hasseDiagram e.enumDef,
            .newline, .newline ]
    def_ :: orderParts
  let fnParts := reg.fns.map fun f =>
    Latex.seq [f.fnDef.formalDefLatex ctx,
               .newline, .newline]
  let propParts := reg.properties.map fun p =>
    Latex.seq [p.propertyDef.formalDefLatex ctx,
               .newline, .newline]
  .seq (descrParts ++ structParts ++ enumParts
    ++ fnParts ++ propParts)

/-- Build the LaTeX sections for a single crate prefix,
    grouped by module. -/
private def crateLatex
    (crate : String) (reg : Registry) (ctx : RenderCtx)
    : Latex :=
  let crateReg := reg.restrictToCrate crate
  let allMods := crateReg.moduleNames
  -- Subsections are modules directly under the crate
  -- (depth 2), e.g. `OpSem.Expressions`. Anything deeper
  -- becomes a subsubsection within its depth-2 ancestor.
  let topMods := allMods.filter fun m => modDepth m == 2
  let buildBody := fun (mod : Lean.Name) =>
    moduleBodyLatex (crateReg.restrictToModule mod) ctx
  let sectionHeader := Latex.section (.raw crate)
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

/-- Build the `RenderCtx` shared by every section of the
    presentation from a full `Registry`. -/
private def mkRenderCtx (reg : Registry) : RenderCtx :=
  let fnNameSet : List String :=
    reg.fns.map (·.fnDef.name)
      ++ reg.properties.map (·.propertyDef.fnDef.name)
  -- Build a table of `(shortName, qualifiedName)` pairs where
  -- the qualified name is `EnumName.variantName`. This is
  -- used to resolve constructor references to their
  -- fully-qualified anchors, so that variants with the same
  -- short name in different enums (e.g. `Value.tuple` and
  -- `ValueExpr.tuple`) can be linked independently.
  let ctorPairs : List (String × String) :=
    reg.enums.flatMap fun e =>
      e.enumDef.variants.map fun v =>
        (v.name.name,
         s!"{e.enumDef.name.name}.{v.name.name}")
  let typeNameSet : List String :=
    reg.enums.map (·.enumDef.name.name)
      ++ reg.structs.map (·.structDef.name)
  let resolveCtor : String → Option String := fun n =>
    if n.contains '.' then
      if ctorPairs.any (·.2 == n) then some n
      else none
    else
      (ctorPairs.find? (·.1 == n)).map (·.2)
  let resolveVariant : String → Option VariantDef := fun n =>
    (resolveCtor n).bind fun q =>
      match q.splitOn "." with
      | [enumName, varName] =>
        (reg.enums.find? (·.enumDef.name.name == enumName)).bind
          fun e => e.enumDef.variants.find?
            (·.name.name == varName)
      | _ => none
  { ctorDisplay := mkCtorDisplay reg.enums
    variants := reg.enums.flatMap (·.enumDef.variants)
    knownFns := fun n => fnNameSet.contains n
    -- Resolve a constructor reference to its fully-qualified
    -- name. Accepts either short (`int`) or already-qualified
    -- (`Value.int`) forms. Returns `none` if the name does
    -- not resolve to any known variant.
    resolveCtor := resolveCtor
    resolveVariant := resolveVariant
    knownTypes := fun n => typeNameSet.contains n
    precondShortUsage := fun nm args =>
      (reg.properties.find?
          (·.propertyDef.fnDef.name == nm)).map
        fun rp => rp.propertyDef.doc args }

/-- Build the full presentation LaTeX body. -/
def buildPresentationLatex (reg : Registry) : Latex :=
  let sectionOrder := ["MIR", "OpSem", "PCG"]
  let allPrefixes := reg.cratePrefixes
  let prefixes :=
    sectionOrder.filter allPrefixes.contains ++
      allPrefixes.filter (! sectionOrder.contains ·)
  let ctx := mkRenderCtx reg
  let sections := prefixes.map
    fun p => crateLatex p reg ctx
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

/-- Page geometry. `article`'s default ~1.5in side margins
    waste a lot of horizontal space — shrink to 1in on all
    sides so wide display-math (e.g. struct-field tables and
    `\begin{array}` blocks) doesn't overflow. -/
private def geometrySetup : Latex :=
  .seq [
    .raw "\\usepackage[margin=1in]{geometry}\n"
  ]

/-- Extra LaTeX preamble (theorem definitions, etc).

    Link styling set up here:

    * `\dashuline` is redefined to produce a dense, grey
      dashed underline (via `ulem`'s `\markoverwith`). It
      is applied automatically to intra-document links
      (targets starting with `#`) — see
      `Latex.internalLink`.
    * External hyperlinks get a solid blue underline via
      `\uline` wrapped in `\textcolor{blue}{...}` — see
      `Latex.externalLink`.

    Callers using `Doc.link` should pass the link body
    unstyled; the backend applies the appropriate
    underline based on whether the target is internal
    or external. -/
def latexPreamble : Latex :=
  .seq [
    geometrySetup,
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
