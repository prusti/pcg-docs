import Core.Dsl.Types.FnDef

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
    let name : LatexMath := .text (.text p.fnDef.name)
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
    property. -/
private def whereBlock (p : PropertyDef) : Latex :=
  if p.fnDef.params.isEmpty then .seq []
  else
    let paramRows := p.fnDef.params.map fun f =>
      [ .escaped f.name
      , .seq [.raw " \\in ",
              f.ty.toLatexMath (fun _ => false)]
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
    let rows : List LatexMath := arms.map fun arm =>
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

/-- Render the property as a LaTeX `definition` environment
    containing the prose description and a single boxed
    display-math equation `LHS := body \quad where p ∈ T,
    …`. Properties no longer emit a separate `\begin{algorithm}`
    float; the formal predicate sits directly under the
    English description.

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
  let lhs := lhsMath p
  let body := bodyMath p ctx
  let equation : LatexMath :=
    .seq [lhs, .raw " \\mathrel{:=} ", body]
  .envOpts "definition" (.text p.fnDef.name) (.seq [
    propertyAnchor, fnAnchor, .newline,
    p.defaultDoc.toLatex, .newline,
    .displayMath equation, .newline,
    whereBlock p
  ])

end PropertyDef
