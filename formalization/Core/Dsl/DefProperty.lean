import Core.Dsl.DefFn
import Core.Dsl.ElabUtils
import Core.Dsl.IdentRefs

open Core.Dsl.IdentRefs

open Core.Dsl.ElabUtils

open Lean in

/-- Human-readable `Doc` description of a property. Two of
    these appear in every `defProperty` after the symbol doc:
    a `short` form (used in `Require` preconditions, rendered
    as a hyperlink to the long form) and a `long` form (used
    in the property's definition box). The body is just a
    `Doc` expression; references to the property's parameters
    use the same names as the `(name : Type)` binders below,
    so e.g. `connected (pd : PcgData …) (a b : PcgNode …)`
    can write `(.seq [a, …, b, …, pd])` directly. The body
    must be wrapped in parentheses so the grammar is
    unambiguous. -/
syntax docDescr := "(" term ")"

/-- Pattern-matching property. -/
syntax "defProperty " ident "(" term ")"
    "short " docDescr
    "long " docDescr
    fnParam* ("displayed " "(" displayPart,+ ")")?
    "where" fnArm*
    : command

/-- Body of an expression-form property: either direct
    `:= expr` or do-block `begin … return expr`. -/
declare_syntax_cat propertyBody
syntax ":=" fnExpr : propertyBody
syntax "begin" fnStmt* "return " fnExpr : propertyBody

/-- Expression-form property (direct or do-block). -/
syntax "defProperty " ident "(" term ")"
    "short " docDescr
    "long " docDescr
    fnParam* ("displayed " "(" displayPart,+ ")")?
    propertyBody
    : command

-- ══════════════════════════════════════════════
-- Shared helpers
-- ══════════════════════════════════════════════

open LeanAST in
/-- Convert raw syntax type to a `LeanTy`. -/
private def syntaxToLeanTy (pt : Lean.Syntax) : LeanTy :=
  (DSLType.parse (toTypeStr pt)).toLeanAST

open LeanAST in
/-- Build `LeanBinder` list from parsed parameter data. -/
private def paramToLeanBinders
    (paramData : Array (Lean.Ident × Lean.TSyntax `term
      × Lean.Syntax))
    : List LeanBinder :=
  paramData.toList.map fun (pn, _, pt) =>
    { name := toString pn.getId
      type := syntaxToLeanTy pt }

open LeanAST in
open Lean Elab Command in
/-- Build a `LeanDecl` string from a property definition
    and parse+elaborate it. -/
private def elabPropertyDecl
    (name : Ident)
    (params : List LeanBinder)
    (body : LeanFnBody)
    : CommandElabM Unit := do
  let decl := LeanDecl.def_ {
    name := toString name.getId
    params
    precondBinds := []
    retType := .const "Prop"
    body
  }
  let defStr := toString decl
  let env ← getEnv
  match Parser.runParserCategory env `command
    defStr with
  | .ok stx =>
    let stx := graftUserNameToken name.getId name.raw stx
    -- Splice each user-source `proof[…]` body in over its
    -- `dslProofMarker (…)` placeholder so the InfoView reports
    -- the proof goal at the user's cursor.
    let userProofs ← takeProofSyntaxes
    let (stx, _) := graftDslProofMarkers userProofs stx
    -- Splice each parameter binder, `let`-binding pat, and
    -- variable usage's user-source syntax over its rendered
    -- ident so LSP gotoDef on a local in the property body
    -- navigates to its binder. Pass `userProofs` so spliced
    -- proof-body subtrees are skipped (preserving e.g. the
    -- user position of a `let`-bound name referenced from
    -- inside a `proof[…]` body).
    let stx ← graftLocalIdentsFromBuffers userProofs stx
    elabCommand stx
  | .error e =>
    drainAllParseBuffers
    throwError
      s!"defProperty: parse error: {e}\n\
        ---\n{defStr}\n---"

open Lean Elab Command in
private def buildPropertyDef
    (name : Ident)
    (symDoc : TSyntax `term)
    (paramData : Array (Ident × TSyntax `term
      × Syntax))
    (body : TSyntax `term)
    (shortBinders : Array Ident)
    (shortExpr : TSyntax `term)
    (docBinders : Array Ident)
    (docExpr : TSyntax `term)
    (display : Option (TSyntax `term) := none)
    : CommandElabM Unit := do
  let paramDefs ← paramData.mapM
    fun (pn, pd, pt) => do
      let ns : TSyntax `term :=
        quote (toString pn.getId)
      let tyTerm ← `(DSLType.parse $(quote (toTypeStr pt)))
      `({ name := $ns, ty := $tyTerm,
          doc := ($pd : Doc) : FieldDef })
  let ns : TSyntax `term :=
    quote (toString name.getId)
  let retTn ← `(DSLType.prim .bool)
  let paramList ← `([$[$paramDefs],*])
  let propDefId := mkIdent (name.getId ++ `propertyDef)
  let docFn ← `(fun (ds : List Doc) =>
      match ds with
      | [$[$docBinders:ident],*] => ($docExpr : Doc)
      | _ => Doc.plain "")
  let shortFn ← `(fun (ds : List Doc) =>
      match ds with
      | [$[$shortBinders:ident],*] => ($shortExpr : Doc)
      | _ => Doc.plain "")
  let displayTerm ← buildDisplayTerm display
  elabCommand (← `(command|
    def $propDefId : PropertyDef :=
      { fnDef :=
          { name := $ns,
            symbolDoc := ($symDoc : Doc),
            doc := Doc.plain "",
            params := $paramList,
            returnType := $retTn,
            body := $body,
            display := $displayTerm },
        doc := $docFn,
        shortDoc := $shortFn }))
  registerInCurrentModule ``registerPropertyDef propDefId

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
open LeanAST in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term)
       short ($shortExpr:term)
       long ($docExpr:term)
       $ps:fnParam*
       $[displayed ( $dps:displayPart,* )]?
       where $arms:fnArm*) => do
    DslLint.lintDocTerm shortExpr
    DslLint.lintDocTerm docExpr
    clearAllParseBuffers
    let paramData ← ps.mapM parseFnParam
    for (pn, _, _) in paramData do
      recordLocalBinder pn pn.getId
    for (_, _, ty) in paramData do recordTypeIdents ty
    let shortBinders := paramData.map (·.1)
    let docBinders := shortBinders
    let displayTerm ← parseFnDisplayOpt paramData dps
    let parsed ← arms.mapM parseFnArm
    let armsList : List (List BodyPat × DslExpr) :=
      parsed.toList.map fun (a, r) => (a.toList, r)
    if DslLint.matchIsIrrefutable armsList then
      Lean.throwErrorAt name DslLint.irrefutableWhereMessage
    let params := paramToLeanBinders paramData
    -- Rewrite each arm's RHS so a top-level
    -- `A₁ ∧ … ∧ Aₙ → G` becomes a named-binder Pi chain;
    -- mirrors `elabExprProperty`. No-op for atomic Prop arms.
    -- `withProofMarkers := true` wraps each `proof[…]` body
    -- in a `dslProofMarker` placeholder so the
    -- `graftDslProofMarkers` pass in `elabPropertyDecl` can
    -- splice the user-source syntax back in.
    let armASTs : List LeanMatchArm :=
      parsed.toList.map fun (patAst, rhsAst) =>
        .mk (patAst.toList.map BodyPat.toLeanAST)
            ((rhsAst.bindAntecedentNames
                (withProofMarkers := true)).toLeanASTWith ""
              [] [] (withProofMarkers := true))
    let lastIsCatchAll := match parsed.back? with
      | some (pats, _) => pats.all fun p =>
          match p with
          | .wild | .var _ => true | _ => false
      | none => false
    let allArms :=
      if lastIsCatchAll then armASTs
      else
        let wildPats := params.map fun _ => LeanPat.wild
        armASTs ++ [.mk wildPats (.ident "False")]
    elabPropertyDecl name params (.matchArms allArms)
    setUserDeclRanges name (← getRef)
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quote rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildPropertyDef name symDoc paramData
      bodyTerm shortBinders shortExpr docBinders docExpr
      (display := displayTerm)
    flushIdentRefs

-- ══════════════════════════════════════════════
-- Expression form (direct and do-block)
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
/-- Shared elaboration for expression-bodied properties.

    For the in-tree Lean elaboration, the antecedent of a
    `∀ vars, A₁ ∧ … ∧ Aₙ → G` body is rewritten into a chain
    of named `(hᵢ : Aᵢ)` Pi binders (see
    `DslExpr.bindAntecedentNames`) so each conjunct's proof is
    in scope for any `proof[hᵢ]` reference. The DSL
    registry entry retains the original AST so the LaTeX
    rendering still shows the conjunction. -/
private def elabExprProperty
    (name : Ident)
    (symDoc : TSyntax `term)
    (paramData : Array (Ident × TSyntax `term × Syntax))
    (rhsAst : DslExpr)
    (shortBinders : Array Ident)
    (shortExpr : TSyntax `term)
    (docBinders : Array Ident)
    (docExpr : TSyntax `term)
    (display : Option (TSyntax `term) := none)
    : CommandElabM Unit := do
  let params := paramToLeanBinders paramData
  -- `withProofMarkers := true` wraps each `proof[…]` body in
  -- a `dslProofMarker` placeholder so `graftDslProofMarkers`
  -- inside `elabPropertyDecl` can splice the user-source
  -- syntax back in over the parsed-from-string copy.
  let body :=
    LeanAST.LeanFnBody.expr
      ((rhsAst.bindAntecedentNames
          (withProofMarkers := true)).toLeanASTWith ""
        [] [] (withProofMarkers := true))
  elabPropertyDecl name params body
  let bodyTerm ←
    `(FnBody.expr $(quote rhsAst))
  buildPropertyDef name symDoc paramData
    bodyTerm shortBinders shortExpr docBinders docExpr
    (display := display)

open Lean Elab Command Term in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term)
       short ($shortExpr:term)
       long ($docExpr:term)
       $ps:fnParam*
       $[displayed ( $dps:displayPart,* )]?
       $body:propertyBody) => do
    DslLint.lintDocTerm shortExpr
    DslLint.lintDocTerm docExpr
    clearAllParseBuffers
    let paramData ← ps.mapM parseFnParam
    for (pn, _, _) in paramData do
      recordLocalBinder pn pn.getId
    for (_, _, ty) in paramData do recordTypeIdents ty
    let shortBinders := paramData.map (·.1)
    let docBinders := shortBinders
    let displayTerm ← parseFnDisplayOpt paramData dps
    let rhsAst ← match body with
      | `(propertyBody| := $rhs:fnExpr) => parseExpr rhs
      | `(propertyBody|
          begin $stmts:fnStmt* return $ret:fnExpr) =>
        parseStmtsAsExpr stmts (← parseExpr ret)
      | _ => throwError "invalid propertyBody"
    -- Lint pass: every diagnostic surfaces as a build-time
    -- error attached to the property's name token, so the
    -- offending property is easy to locate in the user's
    -- file. Currently flags `mergeableBinders` (e.g.
    -- `m' ∈ Machine, m ∈ Machine` should be `m' m ∈ Machine`).
    for diag in DslLint.lintExpr rhsAst do
      Lean.throwErrorAt name diag.message
    elabExprProperty name symDoc paramData
      rhsAst shortBinders shortExpr docBinders docExpr
      (display := displayTerm)
    setUserDeclRanges name (← getRef)
    flushIdentRefs
