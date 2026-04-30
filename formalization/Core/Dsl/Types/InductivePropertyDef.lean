import Core.Export.Latex
import Core.Dsl.Types.DslExpr
import Core.Dsl.Types.RenderCtx
import Core.Dsl.Types.StructDef

/-- A binder appearing in an inductive-property rule, e.g.
    `cap : InitialisationState` inside `{cap : InitialisationState}`.
    The `type` is stored as the printed Lean text so that we can
    splice the binder verbatim back into the generated `inductive`
    declaration without round-tripping through `DSLType`. -/
structure InductiveRuleBinder where
  /-- Bound name. -/
  name : String
  /-- Optional type annotation (raw Lean source). -/
  type : Option String
  deriving Repr

/-- A single inference-rule of an inductive property: a list of
    quantified binders, a list of premises (structured DSL
    expressions), and the rule's conclusion (also a DSL
    expression).

    Storing premises and the conclusion as `DslExpr` lets the
    LaTeX backend render constructor and function references as
    hyperlinks and use math notation for operators (`∈`, `≠`, …)
    rather than dumping raw Lean source. -/
structure InductiveRule where
  /-- Constructor name (e.g. `"leaf"`, `"fields"`). -/
  name : String
  /-- Universally-quantified binders (rendered above the line as
      a side-condition like `cap, fs, x`). -/
  binders : List InductiveRuleBinder
  /-- Premises rendered above the inference line, separated by
      thin spaces. -/
  premises : List DslExpr
  /-- Rule conclusion: the predicate applied to its indices. -/
  conclusion : DslExpr
  deriving Repr

/-- An exportable inductive-property definition. Produces a Lean
    `inductive Name … : Prop` in both the in-tree and generated
    Lean projects, and a sequence of `\inferrule`-rendered
    inference rules in the LaTeX presentation. The Rust exporter
    skips these (Prop-level, no runtime payload). -/
structure InductivePropertyDef where
  /-- The property name (e.g. `"HasNonDeepLeaf"`). -/
  name : String
  /-- LaTeX definition title (e.g. `"Has Non-Deep Leaf"`). -/
  docParam : String
  /-- Top-level documentation. -/
  doc : Doc
  /-- Implicit type parameters (rare for a Prop, but supported
      symmetrically with `defStruct` / `defEnum`). -/
  typeParams : List String := []
  /-- The property's indices (each becomes an explicit binder in
      the generated `inductive Name (…) : Prop`). -/
  params : List FieldDef
  /-- The inference rules. -/
  rules : List InductiveRule
  /-- Optional custom display template for applied uses of the
      property. When set, a call `Name ‹a, b, …›` (e.g. in a
      rule conclusion or another property's body) renders the
      template with each `#param` reference replaced by the
      rendered argument at the matching positional slot, just
      like `defFn`'s display template. When `none`, the call
      falls back to the default `Name(args)` rendering. -/
  display : Option (List DisplayPart) := none
  /-- Pre-rendered Lean source for the underlying
      `inductive Name … : Prop where | …` declaration. The
      DSL command precomputes this so the LeanExport pipeline
      need not re-derive Lean type strings (which would
      require importing the Lean exporter and creating a
      circular dependency between `Core/Dsl/Types/` and
      `Core/Export/Lean.lean`). -/
  leanSource : String := ""
  deriving Repr

namespace InductivePropertyDef

/-- Render a DSL expression as `LatexMath` using
    `DslExpr.toDoc` so constructor and function references
    become hyperlinks and operators use math notation.
    `ctx` supplies the renderer's constructor/function
    resolution; `fnName` is used for self-reference. -/
private def exprLatex
    (ctx : RenderCtx) (fnName : String) (e : DslExpr)
    : LatexMath :=
  -- `isProperty := true` switches boolean literals and
  -- related atoms to their Prop-mode presentations.
  (DslExpr.toDoc fnName ctx (fun _ => none) true e).toLatexMath

/-- Render a single rule as a `\inferrule`. Premises sit
    above the inference line (separated by `\\\\`),
    conclusion below. -/
private def ruleLatex
    (ctx : RenderCtx) (fnName : String) (r : InductiveRule)
    : Latex :=
  -- `\inferrule*` premises and conclusion sit inside `}{…}`
  -- braces; multi-line content there breaks the macro. Disable
  -- formatting-hint breaks for both via `allowBreak := false`.
  let inlineCtx := { ctx with allowBreak := false }
  let premiseLines : List LatexMath :=
    r.premises.map (exprLatex inlineCtx fnName)
  let premises : LatexMath :=
    if r.premises.isEmpty then .raw ""
    else
      LatexMath.intercalate (.raw " \\\\ ") premiseLines
  let conclusion : LatexMath := exprLatex inlineCtx fnName r.conclusion
  let inference : LatexMath :=
    -- The `Right=` label of `\inferrule*` is rendered in text
    -- mode, so use a raw plain string for the rule name.
    .seq [
      .raw "\\inferrule*[Right=\\textsc{",
      .raw (r.name.replace "_" "\\_"),
      .raw "}]{",
      premises,
      .raw "}{",
      conclusion,
      .raw "}" ]
  Latex.displayMath inference

/-- Render the inductive property as a LaTeX `definition`
    environment (prose) followed by one `\inferrule` per rule.

    The header is written in natural relational form, mirroring
    how the property is referenced in math:
    * 1 param  : `Name(p)`
    * 2 params : `p₁ Name p₂` (infix)
    * otherwise: `Name(p₁, …, pₙ)`
    A trailing `where` block then binds each parameter to its
    type via `∈`, one row per parameter (mirroring `defStruct`),
    so the param docs and types are easy to scan when there are
    several. -/
def formalDefLatex
    (p : InductivePropertyDef) (ctx : RenderCtx) : Latex :=
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{p.name}}\{}"
  let nameLatex : LatexMath := .text (.text p.name)
  let paramName (f : FieldDef) : LatexMath := .escaped f.name
  -- When a `displayed` template is supplied, use it for the
  -- header (with arg references rendered as their parameter
  -- name, since the `where`-block below introduces those names
  -- explicitly). Otherwise the header follows
  -- `PRESENTATION_PROP_APP_STYLE` — `Haskell` produces
  -- `Name p₁ p₂ …`; `Rust` keeps the previous `Name(p)` /
  -- `p₁ Name p₂` (infix for binary) / `Name(p₁, …, pₙ)` shape.
  let header : LatexMath := match p.display with
    | some parts =>
      .seq (parts.map fun
        | .lit d => d.toLatexMath
        | .arg name _ => .escaped name)
    | none =>
      if p.params.isEmpty then nameLatex
      else if PRESENTATION_PROP_APP_STYLE == .Haskell then
        let args := LatexMath.intercalate (.raw "~")
          (p.params.map paramName)
        .seq [nameLatex, .raw "~", args]
      else match p.params with
        | [a] =>
          .seq [nameLatex, .raw "(", paramName a, .raw ")"]
        | [a, b] =>
          .seq [paramName a, .raw "~", nameLatex, .raw "~",
                paramName b]
        | xs =>
          let args := LatexMath.intercalate (.raw ", ")
            (xs.map paramName)
          .seq [nameLatex, .raw "(", args, .raw ")"]
  let whereBlock : Latex :=
    if p.params.isEmpty then .seq []
    else
      let paramRows := p.params.map fun f =>
        [ paramName f
        , .seq [.raw " \\in ",
                f.ty.toLatexMath (fun _ => false)]
        , -- Wrap the description in a `\parbox` so long
          -- param descriptions wrap onto multiple lines
          -- instead of overflowing the array row, mirroring
          -- the `defStruct` field-row layout.
          .seq [.raw "~", .text (Latex.parbox
            "\\dimexpr\\linewidth-9cm\\relax"
            (.seq [.raw "(", f.doc.toLatex, .raw ")"]))]
        ]
      .seq [.raw "where", .newline,
            .displayMath (.array none "rll" paramRows),
            .newline]
  let prose : Latex := .seq [p.doc.toLatex, .newline]
  let defBlock : Latex :=
    .envOpts "definition" (.text p.docParam) (.seq [
      typeTarget, .newline,
      .displayMath header, .newline,
      whereBlock ])
  let rulesBlock : Latex :=
    .seq (p.rules.map (ruleLatex ctx p.name)
      |>.intersperse .newline)
  .seq [prose, defBlock, .newline, rulesBlock, .newline]

end InductivePropertyDef
