import Core.Export.Latex
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.DslExpr
import Core.Dsl.Types.RenderCtx
import Core.Dsl.DslType

/-- A match arm: patterns → expression. -/
structure BodyArm where
  pat : List BodyPat
  rhs : DslExpr
  deriving Repr

/-- A function body: either pattern-matching arms or
    a direct expression. -/
inductive FnBody where
  /-- Pattern-matching function. -/
  | matchArms (arms : List BodyArm)
  /-- Direct expression (no pattern match needed). -/
  | expr (body : DslExpr)
  deriving Repr

/-- A precondition applied to specific arguments. -/
structure Precondition where
  /-- The property name. -/
  name : String
  /-- The argument names to apply the property to. -/
  args : List String
  deriving Repr

/-- An exportable function definition. -/
structure FnDef where
  name : String
  symbolDoc : Doc
  doc : Doc
  params : List FieldDef
  returnType : DSLType
  /-- Preconditions that must hold before calling
      this function. -/
  preconditions : List Precondition := []
  body : FnBody
  /-- When set, this function is part of a mutual-recursion
      group identified by the given tag. The Lean backend
      emits all functions sharing a tag together inside a
      single `mutual … end` block. -/
  mutualGroup : Option String := none
  /-- Optional custom display template for the function
      signature. When set, the LaTeX presentation renders the
      caption using this template (an interleaving of literal
      math fragments and parameter references) instead of the
      default `name(p₁, p₂, …)` form. Argument references
      use the parameter's auto-looked-up `symbolDoc` (or an
      explicit one supplied at the call site), mirroring
      enum-variant display templates. -/
  display : Option (List DisplayPart) := none
  deriving Repr

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    .seq [.plain s!"{p.name} : ", p.ty.toDoc .normal]
  .seq [ f.symbolDoc, .plain "(",
    Doc.intercalate (.plain ", ") paramDocs,
    .plain ") → ", f.returnType.toDoc .normal ]

/-- Render the function's custom display template to
    `LatexMath`, or `none` if no template was supplied. -/
def displayLatexMath? (f : FnDef) : Option LatexMath :=
  f.display.map fun parts =>
    .seq (parts.map DisplayPart.toLatexMath)

/-- Render a single `DslExpr` as a list of `\State` lines for
    the algorithmic environment. Used both for `expr`-bodied
    function definitions (called at the top level with depth 0)
    and for the rhs of complex match arms in `matchArms`-bodied
    definitions (called with depth 1 inside the enclosing arm).

    `varDisplay`, `ctorDisplay`, `resolveCtor`, and
    `resolveVariant` carry the per-arm constructor scope when
    rendering a match arm's rhs. For `expr` bodies the function
    has no enclosing arm, so the caller passes `none`-returning
    defaults plus the registry-wide ctor/variant resolvers from
    `ctx`. -/
private partial def exprLines
    (fnName : String)
    (ctx : RenderCtx)
    (isProperty : Bool)
    (varDisplay : String → Option MathDoc)
    (ctorDisplay : String → Option MathDoc)
    (resolveCtor : String → Option String)
    (resolveVariant : String → Option VariantDef)
    (e : DslExpr) (depth : Nat) : List Latex :=
  let goExpr (e : DslExpr) : LatexMath :=
    (DslExpr.toDoc fnName ctx varDisplay isProperty e).toLatexMath
  let goPat (p : BodyPat) : LatexMath :=
    (BodyPat.toDoc ctorDisplay resolveCtor
      resolveVariant ctx.variants p).toLatexMath
  let mkIndent (n : Nat) : LatexMath :=
    .raw (String.join (List.replicate n "\\hskip1.5em "))
  let recur := exprLines fnName ctx isProperty varDisplay
    ctorDisplay resolveCtor resolveVariant
  match e with
  | .letIn pat val rest =>
    let patMath := goPat pat
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , patMath
             , .raw " := "
             , goExpr val ])) ]
    letLine :: recur rest depth
  | .letBindIn pat val rest =>
    let patMath := goPat pat
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , patMath
             , .raw " ", .cmd "leftarrow", .raw " "
             , goExpr val ])) ]
    letLine :: recur rest depth
  | .ifThenElse cond t e =>
    let ifLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "if~")
             , goExpr cond
             , .raw "~", .text (.raw "then") ])) ]
    let thenLines := recur t (depth + 1)
    let elseLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "else") ])) ]
    let elseLines := recur e (depth + 1)
    ifLine :: thenLines ++ elseLine :: elseLines
  | .match_ scrut matchArms =>
    let headerLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "match~")
             , goExpr scrut
             , .raw ":" ])) ]
    -- Classify an arm; simple arms get batched into an
    -- aligned `{ll}` array and complex arms drop to a
    -- `\textbf{case} pat ⇒` header followed by the nested
    -- rhs lines.
    let armEntry
        : (List BodyPat × DslExpr)
        → Sum (LatexMath × LatexMath) (Latex × List Latex) :=
      fun (pats, rhs) =>
        let patMath := LatexMath.intercalate
          (.raw ",~")
          (pats.map goPat)
        let isSimple := match rhs with
          | .letIn .. => false
          | .letBindIn .. => false
          | .match_ .. => false
          | .ifThenElse .. => false
          | _ => true
        if isSimple then .inl (patMath, goExpr rhs)
        else
          let caseLine : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     mkIndent (depth + 1)
                   , .raw "\\text{\\textbf{case}}~"
                   , patMath
                   , .raw "~"
                   , .cmd "Rightarrow" ])) ]
          let rhsLs := recur rhs (depth + 2)
          .inr (caseLine, rhsLs)
    -- Render a batch of consecutive simple arms as one
    -- `\State` carrying a `{ll}` math array so the rows
    -- align on `⇒`. The indent prefix inside the array
    -- reproduces the `depth + 1` indentation used for
    -- standalone case lines.
    let renderSimpleBatch
        (batch : List (LatexMath × LatexMath)) : Latex :=
      let rows : List LatexMath := batch.map fun (pat, rhs) =>
        .seq [ mkIndent (depth + 1)
             , .raw "\\text{\\textbf{case}}~", pat
             , .raw " & ", .cmd "Rightarrow", .raw " "
             , rhs, .raw " \\\\" ]
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               .raw "\\begin{array}{@{}ll@{}}\n"
             , LatexMath.seq (rows.intersperse (.raw "\n"))
             , .raw "\n\\end{array}" ])) ]
    let rec renderArms
        : List (List BodyPat × DslExpr)
        → List (LatexMath × LatexMath) → List Latex
      | [], [] => []
      | [], batch => [renderSimpleBatch batch.reverse]
      | arm :: rest, batch =>
        match armEntry arm with
        | .inl simple =>
          renderArms rest (simple :: batch)
        | .inr (caseLine, rhsLs) =>
          let prefixLs :=
            if batch.isEmpty then []
            else [renderSimpleBatch batch.reverse]
          prefixLs ++ caseLine :: rhsLs ++ renderArms rest []
    headerLine :: renderArms matchArms []
  | e =>
    [.seq [ .raw "    "
          , Latex.state (.inlineMath (.seq [
              mkIndent depth, goExpr e ])) ]]

/-- Render the function as a LaTeX algorithm.

    `labelKey` overrides the `\hypertarget` / `\label` key used
    for this function's anchor. Callers pass a qualified key
    (e.g. `"OwnedState.join"`) for functions whose short name
    collides with another registered function; `none` falls
    back to `f.name`. -/
def formalDefLatex
    (f : FnDef)
    (ctx : RenderCtx := {})
    (isProperty : Bool := false)
    (labelKey : Option String := none)
    : Latex :=
  let paramParts : List Latex := f.params.map fun p =>
    Latex.seq [.text p.name, .raw " : ",
               p.ty.toLatex ctx.knownTypes]
  let paramSig : Latex :=
    .seq (paramParts.intersperse (.raw ", "))
  let displayName := Doc.fnNameDisplay f.name
  let caption : Latex :=
    if isProperty then
      .seq [.raw "Property ", .text displayName,
            .raw "(", paramSig, .raw ")"]
    else
      let retTy := f.returnType.toLatex ctx.knownTypes
      .seq [.text displayName, .raw "(",
            paramSig, .raw ") ",
            .inlineMath (.cmd "to"), .raw " ",
            retTy]
  -- For a pattern that will be matched against `ty`, prefer
  -- resolving short constructor names under that type's
  -- namespace. For example, when `ty` is `ValueExpr`, a
  -- pattern of `.tuple` should resolve to `ValueExpr.tuple`
  -- rather than the first-registered `tuple` constructor.
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
  -- One match arm, classified as either a simple arm with an
  -- inline rhs that can be aligned in a `{ll}` array, or a
  -- complex arm whose rhs spans multiple `\State` lines.
  let armEntry (arm : BodyArm) : Sum (LatexMath × LatexMath) (Latex × List Latex) :=
    -- A bound pattern variable is rendered under its actual
    -- name in expression bodies, even when the matching
    -- variant's display template attaches a symbol to that
    -- arg slot. Substituting the variant's symbol made the
    -- body of e.g. `validProjTy`'s `.ref _ _ pointee` arm
    -- render `pointee` as `τ` (Ty's symbolDoc), which both
    -- shadows the function's own `τ` parameter and loses the
    -- bound variable's identity in the math output.
    let varDisplay : String → Option MathDoc :=
      fun _ => none
    -- Zip each sub-pattern with the corresponding function
    -- parameter's type so short-form ctor references can be
    -- resolved under the parameter's type namespace.
    let patMath := LatexMath.intercalate (.raw ",~")
      (arm.pat.zip (f.params.map (·.ty)) |>.map
        fun (p, ty) =>
          (BodyPat.toDoc ctx.ctorDisplay
            (scopedResolveCtor ty)
            (scopedResolveVariant ty)
            ctx.variants p).toLatexMath)
    let isSimple := match arm.rhs with
      | .letBindIn .. => false
      | .letIn .. => false
      | .ifThenElse .. => false
      | .match_ .. => false
      | _ => true
    if isSimple then
      let rhsMath := (arm.rhs.toDoc f.name ctx
        varDisplay isProperty).toLatexMath
      .inl (patMath, rhsMath)
    else
      -- Complex arm: `\textbf{case} pat ⇒` header followed
      -- by indented rhs lines. Alignment across arms is not
      -- attempted because the multi-line rhs can't live in
      -- a single array cell. The rhs is rendered by
      -- `exprLines` at depth 1 — inner expressions inherit
      -- the registry-wide ctor/variant resolvers from `ctx`,
      -- but variable display in the rhs still resolves
      -- through this arm's `varDisplay`.
      let caseLine : Latex :=
        .seq [ .raw "    "
             , Latex.state (.seq [
                 .textbf (.raw "case"), .raw " "
               , .inlineMath patMath
               , .raw " ", .inlineMath (.cmd "Rightarrow") ]) ]
      let rhsLs := exprLines f.name ctx isProperty varDisplay
        ctx.ctorDisplay ctx.resolveCtor ctx.resolveVariant
        arm.rhs 1
      .inr (caseLine, rhsLs)
  -- Render a run of simple arms as one `\State` carrying a
  -- `{ll}` math array so every row aligns on the `⇒`. The
  -- patterns sit in the left column, `⇒ rhs` in the right.
  -- `\textbf{case}` is wrapped in `\text{}` so it renders
  -- as upright bold inside math mode.
  let renderSimpleBatch
      (batch : List (LatexMath × LatexMath)) : Latex :=
    let rows : List LatexMath := batch.map fun (pat, rhs) =>
      .seq [ .raw "\\text{\\textbf{case}}~", pat
           , .raw " & ", .cmd "Rightarrow", .raw " "
           , rhs, .raw " \\\\" ]
    .seq [ .raw "    "
         , Latex.state (.inlineMath (.seq [
             .raw "\\begin{array}{@{}ll@{}}\n"
           , LatexMath.seq (rows.intersperse (.raw "\n"))
           , .raw "\n\\end{array}" ])) ]
  -- Walk the arms, batching consecutive simple arms so they
  -- share one aligned array, and emitting complex arms
  -- (header + indented rhs lines) as-is.
  let rec renderArms
      : List BodyArm → List (LatexMath × LatexMath) → List Latex
    | [], [] => []
    | [], batch => [renderSimpleBatch batch.reverse]
    | arm :: rest, batch =>
      match armEntry arm with
      | .inl simple =>
        renderArms rest (simple :: batch)
      | .inr (caseLine, rhsLs) =>
        let prefixLs :=
          if batch.isEmpty then []
          else [renderSimpleBatch batch.reverse]
        prefixLs ++ caseLine :: rhsLs ++ renderArms rest []
  let noDisp : String → Option MathDoc := fun _ => none
  let bodyLines : List Latex := match f.body with
    | .matchArms arms => renderArms arms []
    | .expr body => exprLines f.name ctx isProperty noDisp
        ctx.ctorDisplay ctx.resolveCtor ctx.resolveVariant
        body 0
  let precondLines : List Latex :=
    f.preconditions.map fun pc =>
      let argDocs : List Doc :=
        pc.args.map (fun a => Doc.plain a)
      match ctx.precondShortUsage pc.name argDocs with
      | some doc =>
        .seq [ .raw "    "
             , Latex.require_ doc.toLatex ]
      | none =>
        let argsMath := LatexMath.intercalate
          (.raw ", ")
          (pc.args.map LatexMath.escaped)
        -- Link the property name to its definition
        -- (registered under the shared `fn:` label via
        -- `knownFns`).
        let nameMath : LatexMath :=
          let resolveAmbiguous : Option String :=
            ctx.currentFnModule.bind fun mod =>
              let candidate := s!"{mod}.{pc.name}"
              if ctx.knownFnAnchors candidate then some candidate
              else none
          let mkHyperref (tgt : String) : LatexMath :=
            .raw s!"\\text\{\\hyperref[fn:{tgt}]\
                    \{\\dashuline\{{pc.name}}}}"
          if ctx.knownFns pc.name && !ctx.ambiguousFns pc.name then
            mkHyperref pc.name
          else match resolveAmbiguous with
            | some tgt => mkHyperref tgt
            | none =>
              if ctx.knownFns pc.name then
                .raw s!"\\text\{\\dashuline\{{pc.name}}}"
              else .escaped pc.name
        .seq [ .raw "    "
             , Latex.require_ (.inlineMath
                 (.seq [nameMath
                       , .raw "(", argsMath
                       , .raw ")"])) ]
  let allLines := precondLines ++ bodyLines
  let descBlock : List Latex :=
    if f.doc.toPlainText.isEmpty then []
    else [.textit f.doc.toLatex, .newline]
  let displayBlock : List Latex := match f.displayLatexMath? with
    | some disp =>
      [.raw "\\par ",
       .textbf (.text "Rendered as "),
       .inlineMath disp, .raw ".",
       .newline]
    | none => []
  let key := labelKey.getD f.name
  .env "algorithm" (.seq [
    Latex.caption caption, .newline,
    .raw s!"\\hypertarget\{fn:{key}}\{}\\label\{fn:{key}}", .newline,
    .seq descBlock,
    .seq displayBlock,
    .env "algorithmic"
      (.seq [Latex.lines allLines, .newline]),
    .newline
  ])

/-- Render for non-LaTeX (Doc-based). -/
def algorithmDoc (f : FnDef) : Doc :=
  let noDisplay : String → Option MathDoc :=
    fun _ => none
  let header := Doc.seq
    [ f.doc, .plain " ", f.shortSig ]
  let cases := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map fun p =>
          (p.toDoc noDisplay).toLatexMath.render)
      let rhsStr := (arm.rhs.toDoc f.name (varDisplay := noDisplay)).toLatexMath.render
      Doc.plain s!"case {patStr}: return {rhsStr}"
    | .expr body =>
      let rhsStr := (body.toDoc f.name (varDisplay := noDisplay)).toLatexMath.render
      [Doc.plain s!"return {rhsStr}"]
  .seq [header, .line, .itemize cases]

end FnDef
