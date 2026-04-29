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
  let premiseLines : List LatexMath :=
    r.premises.map (exprLatex ctx fnName)
  let premises : LatexMath :=
    if r.premises.isEmpty then .raw ""
    else
      LatexMath.intercalate (.raw " \\\\ ") premiseLines
  let conclusion : LatexMath := exprLatex ctx fnName r.conclusion
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

    The header is written in natural relational form with a
    trailing `where` clause binding each parameter to its type
    via `∈`:
    * 1 param  : `Name(p) where p ∈ T`
    * 2 params : `p₁ Name p₂ where p₁ ∈ T₁, p₂ ∈ T₂` (infix)
    * otherwise: `Name(p₁, …, pₙ) where p₁ ∈ T₁, …, pₙ ∈ Tₙ` -/
def formalDefLatex
    (p : InductivePropertyDef) (ctx : RenderCtx) : Latex :=
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{p.name}}\{}"
  let nameLatex : LatexMath := .text (.text p.name)
  let paramName (f : FieldDef) : LatexMath := .escaped f.name
  let body : LatexMath := match p.params with
    | [] => nameLatex
    | [a] =>
      .seq [nameLatex, .raw "(", paramName a, .raw ")"]
    | [a, b] =>
      .seq [paramName a, .raw "~", nameLatex, .raw "~",
            paramName b]
    | xs =>
      let args := LatexMath.intercalate (.raw ", ")
        (xs.map paramName)
      .seq [nameLatex, .raw "(", args, .raw ")"]
  let whereClause : LatexMath :=
    if p.params.isEmpty then .raw ""
    else
      let bindings : LatexMath :=
        LatexMath.intercalate (.raw ", ")
          (p.params.map fun f =>
            .seq [paramName f, .raw " \\in ",
                  f.ty.toLatexMath (fun _ => false)])
      .seq [.raw "\\quad\\text{where}\\quad ", bindings]
  let header : LatexMath := .seq [body, whereClause]
  let prose : Latex := .seq [p.doc.toLatex, .newline]
  let defBlock : Latex :=
    .envOpts "definition" (.text p.docParam) (.seq [
      typeTarget, .newline,
      .displayMath header, .newline ])
  let rulesBlock : Latex :=
    .seq (p.rules.map (ruleLatex ctx p.name)
      |>.intersperse .newline)
  .seq [prose, defBlock, .newline, rulesBlock, .newline]

end InductivePropertyDef
