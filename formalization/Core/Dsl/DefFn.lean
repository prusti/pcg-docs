import Core.Registry
import Core.Export.Lean
import Lean

open Lean in

declare_syntax_cat fnParam
syntax "(" ident str ":" term ")" : fnParam

declare_syntax_cat fnPat
syntax "_" : fnPat
syntax ident : fnPat
syntax "." ident fnPat* : fnPat
syntax "⟨" fnPat,+ "⟩" : fnPat
syntax "(" fnPat ")" : fnPat
syntax "[" "]" : fnPat
syntax fnPat " :: " fnPat : fnPat

declare_syntax_cat fnExpr
syntax "[" "]" : fnExpr
syntax ident : fnExpr
syntax "(" fnExpr ")" : fnExpr
syntax ident "·" ident : fnExpr
syntax ident "·flatMap" "fun" ident "=>" fnExpr
    : fnExpr
syntax fnExpr " :: " fnExpr : fnExpr
syntax fnExpr " ++ " fnExpr : fnExpr
syntax "Some" fnExpr : fnExpr
syntax "None" : fnExpr
syntax "⟨" fnExpr,+ "⟩" : fnExpr
-- Named struct constructor: Name⟨a, b⟩
syntax ident "⟨" fnExpr,+ "⟩" : fnExpr
-- Field access chain: expr ↦ name
syntax fnExpr "↦" ident : fnExpr
-- Indexing: expr !! expr (for list[idx]?)
syntax fnExpr "!!" fnExpr : fnExpr
-- Function call: fn ‹ arg1, arg2 ›
syntax ident "‹" fnExpr,* "›" : fnExpr
-- FoldlM: expr "·foldlM" ident expr
syntax fnExpr "·foldlM" ident fnExpr : fnExpr

declare_syntax_cat fnArm
syntax "| " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat " => " fnExpr
    : fnArm

declare_syntax_cat fnStmt
syntax "let " ident " := " fnExpr : fnStmt
syntax "let " ident " ← " fnExpr : fnStmt

/-- Pattern-matching function. -/
syntax "defFn " ident "(" term ")" str
    fnParam* ":" term " where" fnArm* : command

/-- Imperative do-block function. -/
syntax "defFn " ident "(" term ")" str
    fnParam* ":" term " begin" fnStmt*
    "return " fnExpr : command

-- ══════════════════════════════════════════════
-- Parsing helpers
-- ══════════════════════════════════════════════

private partial def parsePat
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPat| _) => pure .wild
  | `(fnPat| $n:ident) =>
    pure (.var (toString n.getId))
  | `(fnPat| .$n:ident $args:fnPat*) => do
    let a ← args.mapM parsePat
    pure (.ctor (toString n.getId) a.toList)
  | `(fnPat| ⟨$args:fnPat,*⟩) => do
    let a ← args.getElems.mapM parsePat
    pure (.ctor "⟨⟩" a.toList)
  | `(fnPat| ($p:fnPat)) => parsePat p
  | `(fnPat| [ ]) => pure .nil
  | `(fnPat| $h:fnPat :: $t:fnPat) =>
    pure (.cons (← parsePat h) (← parsePat t))
  | _ => Lean.Elab.throwUnsupportedSyntax

private partial def parseExpr
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyExpr := do
  match stx with
  | `(fnExpr| [ ]) => pure .emptyList
  | `(fnExpr| $n:ident) =>
    let name := toString n.getId
    match name with
    | "true" => pure .true_
    | "false" => pure .false_
    | _ => pure (.var name)
  | `(fnExpr| ($e:fnExpr)) => parseExpr e
  | `(fnExpr| $r:ident · $m:ident) =>
    pure (.dot (.var (toString r.getId))
      (toString m.getId))
  | `(fnExpr| $r:ident ·flatMap fun $p:ident =>
        $b:fnExpr) => do
    pure (.flatMap (.var (toString r.getId))
      (toString p.getId) (← parseExpr b))
  | `(fnExpr| $h:fnExpr :: $t:fnExpr) =>
    pure (.cons (← parseExpr h) (← parseExpr t))
  | `(fnExpr| $l:fnExpr ++ $r:fnExpr) =>
    pure (.append (← parseExpr l) (← parseExpr r))
  | `(fnExpr| Some $e:fnExpr) =>
    pure (.some_ (← parseExpr e))
  | `(fnExpr| None) => pure .none_
  | `(fnExpr| ⟨$args:fnExpr,*⟩) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.mkStruct "" as_.toList)
  | `(fnExpr| $n:ident ⟨$args:fnExpr,*⟩) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.mkStruct (toString n.getId) as_.toList)
  | `(fnExpr| $e:fnExpr ↦ $f:ident) =>
    pure (.field (← parseExpr e) (toString f.getId))
  | `(fnExpr| $e:fnExpr !! $i:fnExpr) =>
    pure (.index (← parseExpr e) (← parseExpr i))
  | `(fnExpr| $fn:ident ‹ $args:fnExpr,* ›) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.call (toString fn.getId) as_.toList)
  | `(fnExpr| $e:fnExpr ·foldlM $fn:ident
        $init:fnExpr) =>
    pure (.foldlM (toString fn.getId)
      (← parseExpr init) (← parseExpr e))
  | _ => Lean.Elab.throwUnsupportedSyntax

private def parseStmt
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyStmt := do
  match stx with
  | `(fnStmt| let $n:ident := $e:fnExpr) =>
    pure (.let_ (toString n.getId) (← parseExpr e))
  | `(fnStmt| let $n:ident ← $e:fnExpr) =>
    pure (.letBind (toString n.getId) (← parseExpr e))
  | _ => Lean.Elab.throwUnsupportedSyntax

private def parseFnParam
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.TSyntax `str
         × Lean.Syntax) := do
  match stx with
  | `(fnParam| ($n:ident $d:str : $t:term)) =>
    pure (n, d, t)
  | _ => Lean.Elab.throwUnsupportedSyntax

-- ══════════════════════════════════════════════
-- Core elaboration helpers
-- ══════════════════════════════════════════════

private def buildFnType
    (paramData : Array (Lean.Ident × Lean.TSyntax `str
      × Lean.Syntax))
    (retTy : Lean.TSyntax `term)
    : Lean.Elab.Command.CommandElabM String := do
  let paramTypeStrs := paramData.map fun (_, _, pt) =>
    if pt.isIdent then toString pt.getId
    else pt.reprint.getD (toString pt)
  let retRepr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  pure (" → ".intercalate paramTypeStrs.toList
    ++ s!" → {retRepr}")

open Lean Elab Command in
private def buildFnDef
    (name : Ident)
    (symDoc : TSyntax `term)
    (doc : TSyntax `str)
    (paramData : Array (Ident × TSyntax `str
      × Syntax))
    (retTy : TSyntax `term)
    (body : TSyntax `term)
    : CommandElabM Unit := do
  let paramDefs ← paramData.mapM
    fun (pn, pd, pt) => do
      let ns : TSyntax `term :=
        quote (toString pn.getId)
      let typeStr :=
        if pt.isIdent then toString pt.getId
        else pt.reprint.getD (toString pt)
      let tyTerm ← `(FType.parse $(quote typeStr))
      `({ name := $ns, ty := $tyTerm,
          doc := $pd : FieldDef })
  let ns : TSyntax `term :=
    quote (toString name.getId)
  let retStr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  let retTn ← `(FType.parse $(quote retStr))
  let paramList ← `([$[$paramDefs],*])
  let fnDefId := mkIdent (name.getId ++ `fnDef)
  elabCommand (← `(command|
    def $fnDefId : FnDef :=
      { name := $ns,
        symbolDoc := ($symDoc : Doc), doc := $doc,
        params := $paramList,
        returnType := $retTn,
        body := $body }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerFnDef $fnDefId $modName))

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* : $retTy:term where
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
    -- Generate Lean def via string parsing
    let tyStr ← buildFnType paramData retTy
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        s!"  | {patStr} => {rhsAst.toLean}"
    let hasListPat := parsed.any fun (pats, _) =>
      pats.any fun p => match p with
        | .cons .. | .nil => true | _ => false
    let defKw := if hasListPat then "partial def"
      else "def"
    let defStr := s!"{defKw} {name.getId} : {tyStr}\n\
      {"\n".intercalate armStrs}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    -- Build FnBody metadata
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quoteExpr rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildFnDef name symDoc doc paramData retTy bodyTerm

-- ══════════════════════════════════════════════
-- Do-block form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* : $retTy:term begin
       $stmts:fnStmt* return $ret:fnExpr) => do
    let paramData ← ps.mapM parseFnParam
    let parsedStmts ← stmts.mapM parseStmt
    let parsedRet ← parseExpr ret
    -- Generate Lean def via string parsing
    let retRepr :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let stmtStrs := parsedStmts.toList.map
      BodyStmt.toLean
    let retStr := s!"  {parsedRet.toLean}"
    let allLines := stmtStrs ++ [retStr]
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {tyStr})")
    let defStr := s!"def {name.getId} \
      {paramBinds} : {retRepr} := do\n\
      {"\n".intercalate allLines}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    -- Build FnBody metadata
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
    buildFnDef name symDoc doc paramData retTy bodyTerm
