import Core.Dsl.DefFn

open Lean in

/-- LaTeX description of a property, parameterised by
    one `Doc` binder per input parameter. -/
syntax latexDescr := "latex" "(" ident,* ")" "=>" term

/-- Pattern-matching property. -/
syntax "defProperty " ident "(" term ")" "(" term ")"
    fnParam* latexDescr "where" fnArm*
    : command

/-- Body of an expression-form property: either direct
    `:= expr` or do-block `begin … return expr`. -/
declare_syntax_cat propertyBody
syntax ":=" fnExpr : propertyBody
syntax "begin" fnStmt* "return " fnExpr : propertyBody

/-- Expression-form property (direct or do-block). -/
syntax "defProperty " ident "(" term ")" "(" term ")"
    fnParam* latexDescr propertyBody : command

-- ══════════════════════════════════════════════
-- Shared helpers
-- ══════════════════════════════════════════════

open LeanAST in
/-- Convert raw syntax type to a `LeanTy`. -/
private def syntaxToLeanTy (pt : Lean.Syntax) : LeanTy :=
  let raw :=
    if pt.isIdent then toString pt.getId
    else pt.reprint.getD (toString pt)
  (DSLType.parse raw).toLeanAST

open LeanAST in
/-- Build `LeanBinder` list from parsed parameter data. -/
private def paramToLeanBinders
    (paramData : Array (Lean.Ident × Lean.TSyntax `str
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
  | .ok stx => elabCommand stx
  | .error e =>
    throwError
      s!"defProperty: parse error: {e}\n\
        ---\n{defStr}\n---"

open Lean Elab Command in
private def buildPropertyDef
    (name : Ident)
    (symDoc : TSyntax `term)
    (doc : TSyntax `term)
    (paramData : Array (Ident × TSyntax `str
      × Syntax))
    (body : TSyntax `term)
    (defnBinders : Array Ident)
    (defnDoc : TSyntax `term)
    : CommandElabM Unit := do
  let paramDefs ← paramData.mapM
    fun (pn, pd, pt) => do
      let ns : TSyntax `term :=
        quote (toString pn.getId)
      let typeStr :=
        if pt.isIdent then toString pt.getId
        else pt.reprint.getD (toString pt)
      let tyTerm ← `(DSLType.parse $(quote typeStr))
      `({ name := $ns, ty := $tyTerm,
          doc := $pd : FieldDef })
  let ns : TSyntax `term :=
    quote (toString name.getId)
  let retTn ← `(DSLType.prim .bool)
  let paramList ← `([$[$paramDefs],*])
  let propDefId := mkIdent (name.getId ++ `propertyDef)
  let defnFn ← `(fun (ds : List Doc) =>
      match ds with
      | [$[$defnBinders:ident],*] => ($defnDoc : Doc)
      | _ => Doc.plain "")
  elabCommand (← `(command|
    def $propDefId : PropertyDef :=
      { fnDef :=
          { name := $ns,
            symbolDoc := ($symDoc : Doc),
            doc := ($doc : Doc),
            params := $paramList,
            returnType := $retTn,
            body := $body },
        definition := $defnFn }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerPropertyDef $propDefId $modName))

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
open LeanAST in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam*
       latex ( $defnBinders:ident,* ) => $defnDoc:term
       where $arms:fnArm*) => do
    let paramData ← ps.mapM parseFnParam
    let defnBinders := defnBinders.getElems
    let parsed ← arms.mapM fun arm => match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure (#[← parsePat p], ← parseExpr rhs)
      | _ => throwError "invalid fnArm"
    let params := paramToLeanBinders paramData
    let armASTs : List LeanMatchArm :=
      parsed.toList.map fun (patAst, rhsAst) =>
        .mk (patAst.toList.map BodyPat.toLeanAST)
            rhsAst.toLeanAST
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
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quoteExpr rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildPropertyDef name symDoc doc paramData
      bodyTerm defnBinders defnDoc

-- ══════════════════════════════════════════════
-- Expression form (direct and do-block)
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
/-- Shared elaboration for expression-bodied properties. -/
private def elabExprProperty
    (name : Ident)
    (symDoc : TSyntax `term)
    (doc : TSyntax `term)
    (paramData : Array (Ident × TSyntax `str × Syntax))
    (rhsAst : BodyExpr)
    (defnBinders : Array Ident)
    (defnDoc : TSyntax `term)
    : CommandElabM Unit := do
  let params := paramToLeanBinders paramData
  let body := LeanAST.LeanFnBody.expr rhsAst.toLeanAST
  elabPropertyDecl name params body
  let bodyTerm ←
    `(FnBody.expr $(quoteExpr rhsAst))
  buildPropertyDef name symDoc doc paramData
    bodyTerm defnBinders defnDoc

open Lean Elab Command Term in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam*
       latex ( $defnBinders:ident,* ) => $defnDoc:term
       $body:propertyBody) => do
    let paramData ← ps.mapM parseFnParam
    let defnBinders := defnBinders.getElems
    let rhsAst ← match body with
      | `(propertyBody| := $rhs:fnExpr) => parseExpr rhs
      | `(propertyBody|
          begin $stmts:fnStmt* return $ret:fnExpr) =>
        parseStmtsAsExpr stmts (← parseExpr ret)
      | _ => throwError "invalid propertyBody"
    elabExprProperty name symDoc doc paramData
      rhsAst defnBinders defnDoc
