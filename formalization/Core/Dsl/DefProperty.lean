import Core.Dsl.DefFn

open Lean in

/-- Pattern-matching property. -/
syntax "defProperty " ident "(" term ")" str
    fnParam* "latex" term "where" fnArm*
    : command

/-- Direct expression property. -/
syntax "defProperty " ident "(" term ")" str
    fnParam* "latex" term ":=" fnExpr : command

/-- Do-block property. -/
syntax "defProperty " ident "(" term ")" str
    fnParam* "latex" term "begin" fnStmt*
    "return " fnExpr : command

-- ══════════════════════════════════════════════
-- Shared elaboration helper
-- ══════════════════════════════════════════════

open Lean Elab Command in
private def buildPropertyDef
    (name : Ident)
    (symDoc : TSyntax `term)
    (doc : TSyntax `str)
    (paramData : Array (Ident × TSyntax `str
      × Syntax))
    (body : TSyntax `term)
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
  elabCommand (← `(command|
    def $propDefId : PropertyDef :=
      { fnDef :=
          { name := $ns,
            symbolDoc := ($symDoc : Doc), doc := $doc,
            params := $paramList,
            returnType := $retTn,
            body := $body },
        definition := ($defnDoc : Doc) }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerPropertyDef $propDefId $modName))

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* latex $defnDoc:term where
       $arms:fnArm*) => do
    let paramData ← ps.mapM parseFnParam
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
    let paramTypeStrs := paramData.map fun (_, _, pt) =>
      if pt.isIdent then toString pt.getId
      else pt.reprint.getD (toString pt)
    let tyStr := " → ".intercalate paramTypeStrs.toList
      ++ " → Prop"
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        s!"  | {patStr} => {rhsAst.toLean}"
    let lastIsCatchAll := match parsed.back? with
      | some (pats, _) => pats.all fun p =>
          match p with | .wild | .var _ => true | _ => false
      | none => false
    let allArmStrs :=
      if lastIsCatchAll then armStrs
      else
        let wildPat := ", ".intercalate
          (paramData.toList.map fun _ => "_")
        armStrs ++ [s!"  | {wildPat} => False"]
    let defKw := "def"
    let defStr := s!"{defKw} {name.getId} : {tyStr}\n\
      {"\n".intercalate allArmStrs}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defProperty: parse error: {e}\n\
        ---\n{defStr}\n---"
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quoteExpr rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildPropertyDef name symDoc doc paramData
      bodyTerm defnDoc

-- ══════════════════════════════════════════════
-- Direct expression form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* latex $defnDoc:term :=
       $rhs:fnExpr) => do
    let paramData ← ps.mapM parseFnParam
    let rhsAst ← parseExpr rhs
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {tyStr})")
    let rhsStr := rhsAst.toLean
    let defStr :=
      s!"def {name.getId} {paramBinds} : Prop :=\n\
         {rhsStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defProperty: parse error: {e}\n\
        ---\n{defStr}\n---"
    let bodyTerm ←
      `(FnBody.expr $(quoteExpr rhsAst))
    buildPropertyDef name symDoc doc paramData
      bodyTerm defnDoc

-- ══════════════════════════════════════════════
-- Do-block form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defProperty $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* latex $defnDoc:term begin
       $stmts:fnStmt* return $ret:fnExpr) => do
    let paramData ← ps.mapM parseFnParam
    let parsedStmts ← stmts.mapM parseStmt
    let parsedRet ← parseExpr ret
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {tyStr})")
    let stmtStrs := parsedStmts.toList.map
      BodyStmt.toLean
    let retStr := s!"  {parsedRet.toLean}"
    let allLines := stmtStrs ++ [retStr]
    let defStr := s!"def {name.getId} \
      {paramBinds} : Prop := do\n\
      {"\n".intercalate allLines}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defProperty: parse error: {e}\n\
        ---\n{defStr}\n---"
    let stmtDefs ← parsedStmts.mapM fun s => do
      match s with
      | .let_ n v =>
        `(BodyStmt.let_ $(quote n) $(quoteExpr v))
      | .letBind n v =>
        `(BodyStmt.letBind $(quote n) $(quoteExpr v))
    let stmtList ← `([$[$stmtDefs],*])
    let retQ := quoteExpr parsedRet
    let bodyTerm ←
      `(FnBody.doBlock $stmtList $retQ)
    buildPropertyDef name symDoc doc paramData
      bodyTerm defnDoc
