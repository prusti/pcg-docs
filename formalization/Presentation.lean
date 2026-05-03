import PCG.Analyze
import PCG.AnalysisObject
import PCG.BorrowChecker
import PCG.BorrowsGraph
import PCG.Capability.Order
import PCG.DomainData
import PCG.Edges
import PCG.EvalStmtData
import PCG.EvalStmtPhase
import PCG.Nodes
import PCG.Obtain
import PCG.Owned
import PCG.PcgData
import PCG.PcgDomainData
import PCG.PlaceCapability
import PCG.PlaceExpansion
import PCG.Reachability
import PCG.RequiredGuide
import PCG.TransientState
import PCG.ValidityConditions
import MIR
import Core.Dsl.Types.OrderDef
import Core.Registry

/-- Build a lookup function that maps enum constructor names
    to their `MathDoc` display form. Accepts either a short
    name (e.g. `deref`) or a fully-qualified `EnumName.varName`
    form (e.g. `PcgEdge.deref`); the qualified form is the
    canonical lookup key and avoids ambiguity when several
    enums share a short variant name — for example
    `ProjElem.deref` (display `*`) and `PcgEdge.deref` (which
    takes a `DerefEdge` argument). A short-name lookup falls
    back to the first registered match. -/
private def mkCtorDisplay
    (enums : List RegisteredEnum)
    : String → Option MathDoc :=
  fun ctorName =>
    if ctorName.contains '.' then
      match ctorName.splitOn "." with
      | [enumName, varName] =>
        (enums.find? (·.enumDef.name.name == enumName)).bind
          fun e => (e.enumDef.variants.find?
            (·.name.name == varName)).map (·.displayMathDoc)
      | _ => none
    else
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

/-- Parent module names that act as neutral containers
    (their name would be redundant to repeat in every child's
    subsubsection heading). -/
private def genericParentModules : List String :=
  ["Nodes", "Edges", "Owned", "Obtain", "Analyze"]

/-- Subsubsection title for a nested module: combine the
    module's own last component with its parent's last
    component (e.g. `OpSem.Expressions.Place` →
    `"Place Expressions"`). When the immediate parent is a
    generic container like `Nodes`, use just the child's
    own name — repeating the container adds noise and may
    mis-describe the child (e.g. `PcgPlace Nodes`). -/
private def subsubTitle (n : Lean.Name) : String :=
  let parent := match n.components.dropLast.getLast? with
    | some p => moduleName p
    | none => ""
  if genericParentModules.contains parent then moduleName n
  else s!"{moduleName n} {parent}"

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
    aliases := reg.aliases.filter (·.leanModule == mod)
    orders := reg.orders.filter
      fun o => modEnumNames.contains o.enumName
    fns := reg.fns.filter (·.leanModule == mod)
    properties := reg.properties.filter
      (·.leanModule == mod)
    inductiveProperties := reg.inductiveProperties.filter
      (·.leanModule == mod)
    theorems := reg.theorems.filter
      (·.leanModule == mod)
    -- Template presentations are not module-scoped content;
    -- they're only used by the export pipeline.
    presentations := [] }

/-- Keep only the definitions whose module's root crate
    prefix equals `crate`. -/
def restrictToCrate
    (reg : Registry) (crate : String) : Registry :=
  let p (m : Lean.Name) : Bool :=
    m.getRoot.toString == crate
  { descrs := reg.descrs.filter (fun d => p d.leanModule)
    enums := reg.enums.filter (fun e => p e.leanModule)
    structs := reg.structs.filter (fun s => p s.leanModule)
    aliases := reg.aliases.filter (fun a => p a.leanModule)
    orders := reg.orders
    fns := reg.fns.filter (fun f => p f.leanModule)
    properties := reg.properties.filter
      (fun q => p q.leanModule)
    inductiveProperties := reg.inductiveProperties.filter
      (fun q => p q.leanModule)
    theorems := reg.theorems.filter
      (fun t => p t.leanModule)
    presentations := [] }

/-- Union of every module name that appears in the registry
    (de-duplicated, preserving registration order). -/
def moduleNames (reg : Registry) : List Lean.Name :=
  (reg.descrs.map (·.leanModule)
    ++ reg.structs.map (·.leanModule)
    ++ reg.enums.map (·.leanModule)
    ++ reg.aliases.map (·.leanModule)
    ++ reg.fns.map (·.leanModule)
    ++ reg.properties.map (·.leanModule)
    ++ reg.inductiveProperties.map (·.leanModule)
    ++ reg.theorems.map (·.leanModule)
  ).foldl (init := [])
    fun acc m =>
      if acc.contains m then acc else acc ++ [m]

/-- Union of every crate prefix appearing in the registry. -/
def cratePrefixes (reg : Registry) : List String :=
  (reg.descrs.map (·.leanModule.getRoot.toString)
    ++ reg.enums.map (·.leanModule.getRoot.toString)
    ++ reg.structs.map (·.leanModule.getRoot.toString)
    ++ reg.aliases.map (·.leanModule.getRoot.toString)
    ++ reg.fns.map (·.leanModule.getRoot.toString)
    ++ reg.properties.map (·.leanModule.getRoot.toString)
    ++ reg.inductiveProperties.map
        (·.leanModule.getRoot.toString)
    ++ reg.theorems.map (·.leanModule.getRoot.toString)
  ).foldl (init := [])
    fun acc p =>
      if acc.contains p then acc else acc ++ [p]

end Registry

/-- Build the LaTeX body (no headings) for the items in `reg`,
    rendering each registered descr / struct / alias / enum /
    inductive property / fn / property / theorem in the
    canonical kind order, each followed by two newlines.

    Used both by the per-module section rendering of the full
    presentation and by template presentations, which pass a
    `reg` containing only the curated subset of definitions. -/
def renderRegistryItems
    (reg : Registry) (ctx : RenderCtx) : Latex :=
  let descrParts := reg.descrs.map fun d =>
    Latex.seq [d.doc.toLatex, .newline, .newline]
  let structParts := reg.structs.map fun s =>
    Latex.seq [s.structDef.formalDefLatex ctx.knownTypes,
               .newline, .newline]
  let aliasParts := reg.aliases.map fun a =>
    Latex.seq [a.aliasDef.formalDefLatex ctx.knownTypes,
               .newline, .newline]
  let enumParts := reg.enums.flatMap fun e =>
    let def_ := Latex.seq
      [e.enumDef.formalDefLatex ctx.knownTypes,
       .newline, .newline]
    let orderParts := reg.orders.filter
      (·.enumName == e.enumDef.name.name) |>.map
        fun o =>
          Latex.seq [
            Latex.subsubsection (.raw "Ordering"),
            .newline,
            o.orderDef.hasseDiagram e.enumDef,
            .newline, .newline ]
    def_ :: orderParts
  -- When a function's short name collides with another
  -- registered function, tag its anchor with the module's last
  -- segment (e.g. `OwnedState.meet`) so each `\\label{fn:...}`
  -- is unique.
  let moduleLastSeg (m : Lean.Name) : String :=
    m.components.getLast?.map toString |>.getD m.toString
  let qualifiedLabelKey : Lean.Name → String → Option String :=
    fun mod name =>
      if ctx.ambiguousFns name then
        some s!"{moduleLastSeg mod}.{name}"
      else none
  -- Per-fn ctx: sets `currentFnModule` so unqualified
  -- ambiguous calls inside this fn's body resolve against the
  -- enclosing module.
  let ctxFor : Lean.Name → RenderCtx := fun mod =>
    { ctx with currentFnModule := some (moduleLastSeg mod) }
  -- `defFn`s marked `implicit` are hidden from the LaTeX
  -- presentation: their definition block is omitted, and call
  -- sites render as their lone argument (handled in
  -- `DslExpr.toDoc`).
  let fnParts := reg.fns.filterMap fun f =>
    if f.fnDef.isImplicit then none
    else
      some (Latex.seq
        [f.fnDef.formalDefLatex (ctxFor f.leanModule) false
           (qualifiedLabelKey f.leanModule f.fnDef.name),
         .newline, .newline])
  let propParts := reg.properties.map fun p =>
    Latex.seq [p.propertyDef.formalDefLatex (ctxFor p.leanModule)
                 (qualifiedLabelKey p.leanModule
                   p.propertyDef.fnDef.name),
               .newline, .newline]
  let inductivePropParts :=
    reg.inductiveProperties.map fun p =>
      Latex.seq [p.inductivePropertyDef.formalDefLatex ctx,
                 .newline, .newline]
  let theoremParts :=
    reg.theorems.map fun t =>
      Latex.seq [t.theoremDef.formalDefLatex (ctxFor t.leanModule),
                 .newline, .newline]
  .seq (descrParts ++ structParts ++ aliasParts ++ enumParts
    ++ inductivePropParts ++ fnParts ++ propParts
    ++ theoremParts)

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
    renderRegistryItems (crateReg.restrictToModule mod) ctx
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
    presentation from a `Registry`. Cross-references resolve
    to anchors of names appearing in `reg`; for template
    presentations, callers pass a sub-registry containing only
    the curated subset of definitions, so unresolved
    references stay as plain text rather than dangling
    hyperlinks. -/
def mkRenderCtx (reg : Registry) : RenderCtx :=
  let fnNameSet : List String :=
    reg.fns.map (·.fnDef.name)
      ++ reg.properties.map (·.propertyDef.fnDef.name)
  let fnImplicitSet : List String :=
    reg.fns.filterMap fun f =>
      if f.fnDef.isImplicit then some f.fnDef.name else none
  -- Short names shared by two or more registered functions or
  -- properties. These cannot resolve unambiguously to a single
  -- `\\hypertarget{fn:...}`, so `formalDefLatex` qualifies the
  -- label with the module's last segment (e.g.
  -- `fn:InitTree.meet`) and references resolve through
  -- `DslExpr.fnRef`'s `knownFnAnchors` / `currentFnModule`
  -- lookup rather than the bare short name.
  let ambiguousFnNames : List String :=
    fnNameSet.foldl (init := []) fun acc n =>
      if fnNameSet.count n > 1 && !acc.contains n
      then acc ++ [n] else acc
  let moduleLastSegment (m : Lean.Name) : String :=
    m.components.getLast?.map toString |>.getD m.toString
  -- The set of strings that become `\\hypertarget{fn:...}`
  -- anchors in the LaTeX output: the short name of every
  -- unambiguous fn or property, and the qualified
  -- `{moduleSegment}.{name}` of every ambiguous one.
  let anchorKeyOf (leanMod : Lean.Name) (name : String)
      : String :=
    if ambiguousFnNames.contains name then
      s!"{moduleLastSegment leanMod}.{name}"
    else name
  let knownAnchorSet : List String :=
    (reg.fns.map fun f =>
      anchorKeyOf f.leanModule f.fnDef.name) ++
    (reg.properties.map fun p =>
      anchorKeyOf p.leanModule p.propertyDef.fnDef.name)
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
      ++ reg.aliases.map (·.aliasDef.name)
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
    ambiguousFns := fun n => ambiguousFnNames.contains n
    knownFnAnchors := fun n => knownAnchorSet.contains n
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
        fun rp =>
          Doc.link (rp.propertyDef.shortDoc args)
            s!"#property:{nm}"
    resolveFnDisplay := fun n =>
      let fnHit :=
        (reg.fns.find? (·.fnDef.name == n)).bind fun f =>
          f.fnDef.display.map fun parts =>
            (parts, f.fnDef.params.map (·.name))
      let propHit := fun () =>
        (reg.properties.find?
            (·.propertyDef.fnDef.name == n)).bind fun p =>
          p.propertyDef.fnDef.display.map fun parts =>
            (parts, p.propertyDef.fnDef.params.map (·.name))
      let indHit := fun () =>
        (reg.inductiveProperties.find?
            (·.inductivePropertyDef.name == n)).bind fun ip =>
          ip.inductivePropertyDef.display.map fun parts =>
            (parts, ip.inductivePropertyDef.params.map (·.name))
      (fnHit.orElse propHit).orElse indHit
    inductivePropertyAnchor := fun n =>
      (reg.inductiveProperties.find?
          (·.inductivePropertyDef.name == n)).bind fun ip =>
        ip.inductivePropertyDef.display.map fun _ =>
          s!"fn:{ip.inductivePropertyDef.name}"
    resolveStructDisplay := fun n =>
      (reg.structs.find? (·.structDef.name == n)).bind fun s =>
        s.structDef.display.map fun parts =>
          (parts, s.structDef.fields.map (·.name))
    fnPrecondCount := fun n =>
      let fromFns :=
        (reg.fns.find? (·.fnDef.name == n)).map fun f =>
          f.fnDef.preconditions.length
      let fromProps := fun () =>
        (reg.properties.find? (·.propertyDef.fnDef.name == n)).map
          fun p => p.propertyDef.fnDef.preconditions.length
      (fromFns.orElse fromProps).getD 0
    implicitFns := fun n => fnImplicitSet.contains n }

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
   "placeins", "mathpartir"]

/-- Page geometry. `article`'s default ~1.5in side margins
    waste a lot of horizontal space — shrink to 1in on all
    sides so wide display-math (e.g. struct-field tables and
    `\begin{array}` blocks) doesn't overflow.

    `\emergencystretch` allows TeX to stretch interword space
    by up to 3em when a paragraph would otherwise produce an
    overfull `\hbox` — in particular, paragraphs containing
    an unbreakable `\texttt{...}` token near the line end. -/
private def geometrySetup : Latex :=
  .seq [
    .raw "\\usepackage[margin=1in]{geometry}\n",
    .raw "\\setlength{\\emergencystretch}{3em}\n"
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
    .raw "\\newtheorem{theorem}{Theorem}\n",
    -- Number algorithms, definitions, and theorems per
    -- subsection, so an algorithm/definition/theorem in
    -- subsection 3.8 is rendered as "Algorithm 3.8.1",
    -- "Definition 3.8.1", "Theorem 3.8.1", etc.
    .raw "\\numberwithin{algorithm}{subsection}\n",
    .raw "\\numberwithin{definition}{subsection}\n",
    .raw "\\numberwithin{theorem}{subsection}\n",
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
