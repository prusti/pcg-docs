import Core.Dsl.Types.FnDef
import Core.Dsl.Types.InductivePropertyDef

/-- An exportable property (predicate) definition.

    Wraps a `FnDef` (for Lean/Rust code generation) with a
    parameterised human-readable `Doc`. The `doc` is a
    function of the parameter docs (one `Doc` per input)
    so each call site can weave its own argument names into
    the rendering — used both for the LaTeX definition
    environment and for `Require` preconditions. -/
structure PropertyDef where
  /-- The underlying function definition (returns Bool). -/
  fnDef : FnDef
  /-- Long-form human-readable `Doc` rendering for the
      property's definition box, parameterised by one `Doc`
      per input parameter. -/
  doc : List Doc → Doc
  /-- Short-form `Doc` rendering for `Require` preconditions,
      also parameterised by one `Doc` per input parameter.
      Rendered as a hyperlink to this property's definition
      so a reader can jump from the precondition to the long
      description. -/
  shortDoc : List Doc → Doc
  /-- When `true`, the LaTeX rendering of the property's body
      switches from the default `match … with case … ⇒ …`
      array to a sequence of `\inferrule` blocks — one per
      match arm — mirroring `defInductiveProperty`'s output.
      Each arm contributes a rule whose conclusion is the
      property applied to the arm's pattern(s) and whose
      premise is the arm's right-hand side. RHS literal
      `false` arms are dropped, and a top-level disjunction
      RHS is split into one rule per disjunct. Only
      meaningful when `fnDef.body` is `.matchArms`; ignored
      otherwise. The Lean and Rust outputs are unaffected. -/
  renderAsInductive : Bool := false

namespace PropertyDef

/-- Resolve the `doc` by applying the parameter names
    (as plain `Doc`s) in declaration order. Used for the
    LaTeX definition environment. -/
def defaultDoc (p : PropertyDef) : Doc :=
  p.doc (p.fnDef.params.map fun f => .plain f.name)

/-- Build the LHS of a property's definition equation.

    Mirrors `InductivePropertyDef.formalDefLatex`'s header:
    a custom display template wins; otherwise the LHS follows
    `PRESENTATION_PROP_APP_STYLE` — `Haskell` produces
    `Name p₁ p₂ …` (juxtaposition); `Rust` keeps the previous
    `Name(p)` / `p₁ Name p₂` (infix for binary) /
    `Name(p₁, …, pₙ)` shape. -/
private def lhsMath (p : PropertyDef) : LatexMath :=
  match p.fnDef.displayLatexMath? with
  | some disp => disp
  | none =>
    -- Route the name through `fnNameDisplay` so trailing
    -- prime apostrophes (e.g. `Framing'`) become Unicode
    -- primes, which `escapeLatex` then maps to math-mode
    -- `\ensuremath{'}`. Without this the bare `'` survives
    -- into `\text{Framing'}` and renders as a text-mode
    -- closing single quote rather than a prime.
    let name : LatexMath :=
      .text (.text (Doc.fnNameDisplay p.fnDef.name))
    let argName (f : FieldDef) : LatexMath := .escaped f.name
    if p.fnDef.params.isEmpty then name
    else if PRESENTATION_PROP_APP_STYLE == .Haskell then
      let args := LatexMath.intercalate (.raw "~")
        (p.fnDef.params.map argName)
      .seq [name, .raw "~", args]
    else match p.fnDef.params with
      | [a] =>
        .seq [name, .raw "(", argName a, .raw ")"]
      | [a, b] =>
        .seq [argName a, .raw "~", name, .raw "~", argName b]
      | xs =>
        let args := LatexMath.intercalate (.raw ", ")
          (xs.map argName)
        .seq [name, .raw "(", args, .raw ")"]

/-- Build the `where`-block listing each parameter on its own
    row (binding, type, description) — mirrors `defStruct`'s
    field block. Returns an empty `Latex` for a nullary
    property. `ctx.knownTypes` is threaded into the per-row
    type rendering so each `\in T` clause hyperlinks `T` to
    its `\hypertarget{type:T}` anchor when registered. -/
private def whereBlock (p : PropertyDef) (ctx : RenderCtx) : Latex :=
  if p.fnDef.params.isEmpty then .seq []
  else
    let paramRows := p.fnDef.params.map fun f =>
      [ .escaped f.name
      , .seq [.raw " \\in ",
              f.ty.toLatexMath ctx.knownTypes]
      , -- Wrap the description in a `\parbox` so long param
        -- descriptions wrap onto multiple lines instead of
        -- overflowing the array row, mirroring the
        -- `defStruct` field-row layout.
        .seq [.raw "~", .text (Latex.parbox
          "\\dimexpr\\linewidth-9cm\\relax"
          (.seq [.raw "(", f.doc.toLatex, .raw ")"]))]
      ]
    .seq [.raw "where", .newline,
          .displayMath (.array none "rll" paramRows),
          .newline]

/-- Render the body of a property's definition equation as
    a single `LatexMath`. For an expression body the body
    is rendered through `DslExpr.toDoc`. For a match-arms
    body the result is `\text{match}~params~with` followed
    by a 2-column `array` of `case pat ⇒ rhs` rows
    (mirroring the existing in-algorithmic-env rendering). -/
private def bodyMath
    (p : PropertyDef) (ctx : RenderCtx) : LatexMath :=
  let fnName := p.fnDef.name
  let noDisp : String → Option MathDoc := fun _ => none
  let exprMath (e : DslExpr) : LatexMath :=
    (DslExpr.toDoc fnName ctx noDisp true e).toLatexMath
  match p.fnDef.body with
  | .expr body => exprMath body
  | .matchArms arms =>
    let scopedResolveCtor
        (ty : DSLType) : String → Option String :=
      match ty with
      | .named n => fun name =>
        if name.contains '.' then ctx.resolveCtor name
        else (ctx.resolveCtor s!"{n.name}.{name}").orElse
          fun _ => ctx.resolveCtor name
      | _ => ctx.resolveCtor
    let scopedResolveVariant
        (ty : DSLType) : String → Option VariantDef :=
      match ty with
      | .named n => fun name =>
        if name.contains '.' then ctx.resolveVariant name
        else (ctx.resolveVariant s!"{n.name}.{name}").orElse
          fun _ => ctx.resolveVariant name
      | _ => ctx.resolveVariant
    let paramNames : LatexMath :=
      LatexMath.intercalate (.raw ",~")
        (p.fnDef.params.map fun f => .escaped f.name)
    -- Drop arms gated on a disabled feature (explicit or
    -- variant-inherited; see `BodyArm.effectiveFeatures`).
    -- The walk into nested patterns means a disabled
    -- destructor like `.ref` is hidden even when it sits
    -- alongside another scrutinee pattern in this arm.
    let visibleArms : List BodyArm :=
      arms.filter fun a =>
        !(a.effectiveFeatures ctx).any ctx.isFeatureDisabled
    let rows : List LatexMath := visibleArms.map fun arm =>
      let patMath := LatexMath.intercalate (.raw ",~")
        (arm.pat.zip (p.fnDef.params.map (·.ty)) |>.map
          fun (pat, ty) =>
            (BodyPat.toDoc ctx.ctorDisplay
              (scopedResolveCtor ty)
              (scopedResolveVariant ty)
              ctx.variants pat).toLatexMath)
      let rhsMath := exprMath arm.rhs
      .seq [.raw "\\text{\\textbf{case}}~", patMath,
            .raw " & ", .cmd "Rightarrow", .raw " ",
            rhsMath, .raw " \\\\"]
    .seq [.raw "\\text{match}~", paramNames, .raw "~",
          .raw "\\text{with} ",
          .raw "\\begin{array}{@{}ll@{}}\n",
          LatexMath.seq (rows.intersperse (.raw "\n")),
          .raw "\n\\end{array}"]

/-- Render a single `BodyPat` as `LatexMath`, threading
    the per-parameter type so that constructor names inside
    the pattern (e.g. `.fields` inside an `InitTree` slot)
    resolve against the type's namespace before falling back
    to the global registry. Mirrors the per-arm scoping used
    by `bodyMath`. When `juxtaposition := true`, compound
    patterns (constructor applications, non-list-literal cons
    chains) are wrapped in parentheses so they can sit safely
    next to the property name in a Haskell-style call. -/
private def patLatex
    (ctx : RenderCtx) (ty : DSLType) (pat : BodyPat)
    (juxtaposition : Bool := false)
    : LatexMath :=
  let scopedResolveCtor : String → Option String :=
    match ty with
    | .named n => fun name =>
      if name.contains '.' then ctx.resolveCtor name
      else (ctx.resolveCtor s!"{n.name}.{name}").orElse
        fun _ => ctx.resolveCtor name
    | _ => ctx.resolveCtor
  let scopedResolveVariant : String → Option VariantDef :=
    match ty with
    | .named n => fun name =>
      if name.contains '.' then ctx.resolveVariant name
      else (ctx.resolveVariant s!"{n.name}.{name}").orElse
        fun _ => ctx.resolveVariant name
    | _ => ctx.resolveVariant
  let inner : MathDoc := BodyPat.toDoc ctx.ctorDisplay
    scopedResolveCtor scopedResolveVariant
    ctx.variants pat
  if juxtaposition && pat.needsParen then
    (MathDoc.paren inner).toLatexMath
  else inner.toLatexMath

/-- Build the inductive-form conclusion `Name(pat₁, …, patₙ)`
    for a single match arm: rendered patterns sit in the
    parameter positions of the property's header. A custom
    `displayed` template is honoured by substituting each
    `#paramName` reference with the rendered pattern at the
    matching slot. Mirrors `lhsMath`'s shape selection
    (Haskell juxtaposition, `Rust` parens / infix). -/
private def conclusionLatex
    (p : PropertyDef) (ctx : RenderCtx) (pats : List BodyPat)
    : LatexMath :=
  -- For a Haskell-style header `Name p₁ p₂ …` and for the
  -- one-arg `Name(p)` Rust shape, compound argument patterns
  -- need parens so the application binds correctly. The infix
  -- two-arg Rust shape (`p₁ Name p₂`) already separates its
  -- arguments with the property name and doesn't need
  -- parens. Custom display templates are user-controlled and
  -- handled below without extra parenthesisation.
  let nameLatex : LatexMath :=
    .text (.text (Doc.fnNameDisplay p.fnDef.name))
  let usesJuxtaposition : Bool :=
    p.fnDef.display.isNone &&
      (PRESENTATION_PROP_APP_STYLE == .Haskell ||
        pats.length == 1)
  let patArgs : List LatexMath :=
    pats.zip (p.fnDef.params.map (·.ty)) |>.map fun (pat, ty) =>
      patLatex ctx ty pat (juxtaposition := usesJuxtaposition)
  match p.fnDef.display with
  | some parts =>
    let paramToPat : String → Option LatexMath := fun name =>
      let zipped := p.fnDef.params.zip patArgs
      match zipped.find? (fun (f, _) => f.name == name) with
      | some (_, m) => some m
      | none => none
    .seq (parts.map fun
      | .lit d => d.toLatexMath
      | .arg name symbol =>
        match paramToPat name with
        | some m => m
        | none => symbol.toLatexMath)
  | none =>
    if patArgs.isEmpty then nameLatex
    else if PRESENTATION_PROP_APP_STYLE == .Haskell then
      .seq [nameLatex, .raw "~",
            LatexMath.intercalate (.raw "~") patArgs]
    else match patArgs with
      | [a] => .seq [nameLatex, .raw "(", a, .raw ")"]
      | [a, b] =>
        .seq [a, .raw "~", nameLatex, .raw "~", b]
      | xs =>
        .seq [nameLatex, .raw "(",
              LatexMath.intercalate (.raw ", ") xs, .raw ")"]

/-- Strip the leading anonymous-constructor `.` from a pattern
    constructor name. -/
private def stripCtorDot (n : String) : String :=
  if n.startsWith "." then (n.drop 1).toString else n

/-- Walk the leftmost-deepest constructor chain of a single
    `BodyPat`, collecting short ctor names. Used to derive a
    rule label from a match arm's pattern. -/
private partial def patNameParts : BodyPat → List String
  | .ctor n args =>
    let head := stripCtorDot n
    match args with
    | h :: _ => head :: patNameParts h
    | [] => [head]
  | .cons _ _ => ["cons"]
  | .nil => ["nil"]
  | .wild | .var _ | .natLit _ => []

/-- Derive a stable, human-readable rule label for an arm
    from its patterns: join the leftmost-deepest constructor
    chain across each pattern with `_`. Falls back to
    `caseN` for arms whose patterns are entirely
    irrefutable (`_`, variables). -/
private def patternsRuleName
    (pats : List BodyPat) (idx : Nat) : String :=
  let parts := pats.flatMap patNameParts
  if parts.isEmpty then s!"case{idx + 1}"
  else String.intercalate "_" parts

/-- Decompose the right-hand side of a match arm into a list
    of premise sets, one per inductive rule the arm should
    generate. A literal `false`/`False` produces no rules;
    a top-level disjunction recurses on each branch
    (since `(A ∨ B) → G` is equivalent to two rules
    `A → G` and `B → G`); a literal `true` produces a single
    premise-free rule; everything else becomes one rule with
    the whole expression as its sole premise. -/
private partial def rhsToPremiseSets
    : DslExpr → List (List DslExpr)
  | .false_ => []
  | .true_ => [[]]
  | .or l r => rhsToPremiseSets l ++ rhsToPremiseSets r
  | e => [[e]]

/-- Render the property's `where` arms as a sequence of
    `\inferrule` blocks — one per rule produced by
    `rhsToPremiseSets`. Used in place of `bodyMath` when the
    property is declared `inductively`. Arms gated on a
    disabled feature are dropped before rule expansion. -/
private def inductiveRulesLatex
    (p : PropertyDef) (ctx : RenderCtx) : Latex :=
  let inlineCtx := { ctx with allowBreak := false }
  let arms : List BodyArm := match p.fnDef.body with
    | .matchArms arms => arms
    | .expr _ => []
  let visibleArms : List BodyArm := arms.filter fun a =>
    !(a.effectiveFeatures ctx).any ctx.isFeatureDisabled
  let rules : List Latex :=
    visibleArms.zipIdx.flatMap fun (arm, idx) =>
      let baseName := patternsRuleName arm.pat idx
      let conclusion := conclusionLatex p inlineCtx arm.pat
      let sets := rhsToPremiseSets arm.rhs
      let n := sets.length
      sets.zipIdx.map fun (premiseExprs, j) =>
        let premiseLatex : List LatexMath :=
          premiseExprs.map
            (InductivePropertyDef.exprLatex inlineCtx p.fnDef.name)
        let ruleName :=
          if n ≤ 1 then baseName
          else s!"{baseName}_{j + 1}"
        InductivePropertyDef.renderInferrule
          ruleName premiseLatex conclusion
  Latex.seq (rules.intersperse Latex.newline)

/-- Render the property as a LaTeX `definition` environment
    containing the prose description and a single boxed
    display-math equation `LHS := body \quad where p ∈ T,
    …`. Properties no longer emit a separate `\begin{algorithm}`
    float; the formal predicate sits directly under the
    English description.

    When `p.renderAsInductive` is set, the body is replaced
    by a sequence of `\inferrule` blocks (one per arm, mirroring
    `defInductiveProperty`'s output) and the `where`-block of
    parameter bindings is emitted inside the same `definition`
    environment so types stay visible above the rules.

    `labelKey` overrides the `\hypertarget` / `\label` key
    used for the underlying function's anchor (see
    `FnDef.formalDefLatex`). -/
def formalDefLatex
    (p : PropertyDef)
    (ctx : RenderCtx := {})
    (labelKey : Option String := none)
    : Latex :=
  let key := labelKey.getD p.fnDef.name
  let propertyAnchor : Latex :=
    .raw s!"\\hypertarget\{property:{p.fnDef.name}}\{}"
  let fnAnchor : Latex :=
    .raw s!"\\hypertarget\{fn:{key}}\{}\\label\{fn:{key}}"
  if p.renderAsInductive then
    let header := lhsMath p
    let defBlock : Latex :=
      .envOpts "definition"
          (.text (Doc.fnNameDisplay p.fnDef.name)) (.seq [
        propertyAnchor, fnAnchor, .newline,
        p.defaultDoc.toLatex, .newline,
        .displayMath header, .newline,
        whereBlock p ctx ])
    .seq [defBlock, .newline,
          inductiveRulesLatex p ctx, .newline]
  else
    let lhs := lhsMath p
    let body := bodyMath p ctx
    let equation : LatexMath :=
      .seq [lhs, .raw " \\mathrel{:=} ", body]
    .envOpts "definition"
        (.text (Doc.fnNameDisplay p.fnDef.name)) (.seq [
      propertyAnchor, fnAnchor, .newline,
      p.defaultDoc.toLatex, .newline,
      .displayMath equation, .newline,
      whereBlock p ctx
    ])

end PropertyDef
