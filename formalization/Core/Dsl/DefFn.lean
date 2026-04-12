import Core.Registry
import Core.Export.Lean
import Core.Set
import Lean

open Lean in

declare_syntax_cat fnParam
syntax "(" ident str ":" term ")" : fnParam

declare_syntax_cat fnPat
declare_syntax_cat fnPatAtom
syntax "_" : fnPatAtom
syntax ident : fnPatAtom
syntax num : fnPatAtom
syntax "[" "]" : fnPatAtom
syntax "[" fnPat,+ "]" : fnPatAtom
syntax "⟨" fnPat,+ "⟩" : fnPatAtom
syntax "(" fnPat ")" : fnPatAtom
syntax fnPatAtom : fnPat
syntax "_" : fnPat
syntax ident : fnPat
syntax "." ident fnPatAtom* : fnPat
syntax ident "." ident fnPatAtom* : fnPat
syntax num : fnPat
syntax "⟨" fnPat,+ "⟩" : fnPat
syntax "(" fnPat ")" : fnPat
syntax "[" "]" : fnPat
syntax "[" fnPat,+ "]" : fnPat
syntax fnPat " :: " fnPat : fnPat

declare_syntax_cat fnExpr
syntax "[" "]" : fnExpr
syntax "[" fnExpr,+ "]" : fnExpr
syntax num : fnExpr
syntax ident : fnExpr
syntax "(" fnExpr ")" : fnExpr
syntax fnExpr "·" ident : fnExpr
syntax fnExpr "·flatMap" "fun" ident "=>" fnExpr
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
-- Fallible indexing: expr !! expr (for list[idx]?)
syntax fnExpr "!!" fnExpr : fnExpr
-- Infallible indexing: expr ! expr (for list[idx])
syntax fnExpr "!" fnExpr : fnExpr
-- Function call: fn ‹ arg1, arg2 ›
syntax ident "‹" fnExpr,* "›" : fnExpr
-- FoldlM: expr "·foldlM" ident expr
syntax fnExpr "·foldlM" ident fnExpr : fnExpr
-- Less-than: expr < expr
syntax fnExpr " < " fnExpr : fnExpr
-- Chained less-than: expr < expr < expr
syntax fnExpr " < " fnExpr " < " fnExpr : fnExpr
-- Less-than-or-equal: expr ≤ expr
syntax fnExpr " ≤ " fnExpr : fnExpr
-- Addition: expr + expr
syntax fnExpr " + " fnExpr : fnExpr
syntax fnExpr " - " fnExpr : fnExpr
-- Empty set: ∅
syntax "∅" : fnExpr
-- Set singleton: ⦃ expr ���
syntax "⦃" fnExpr "⦄" : fnExpr
-- Set union: expr ∪ expr
syntax fnExpr " ∪ " fnExpr : fnExpr
-- Set flat-map: expr ·setFlatMap fun ident => expr
syntax fnExpr "·setFlatMap" "fun" ident "=>" fnExpr
    : fnExpr
-- Universal quantifier over a set:
-- expr ·forAll fun ident => expr
syntax fnExpr "·forAll" "fun" ident "=>" fnExpr
    : fnExpr
-- Logical conjunction: expr ∧ expr
syntax fnExpr " ∧ " fnExpr : fnExpr
-- Logical disjunction: expr ∨ expr
syntax fnExpr " ∨ " fnExpr : fnExpr
-- Implication: expr → expr
syntax fnExpr " → " fnExpr : fnExpr
-- Universal quantifier: ∀ ident, expr
syntax "∀∀" ident "," fnExpr : fnExpr
-- Proof placeholder
syntax "sorry" : fnExpr
-- Raw Lean proof term (invisible in Rust/LaTeX)
syntax "lean_proof(" str ")" : fnExpr

declare_syntax_cat fnArm
syntax "| " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat " => " fnExpr
    : fnArm

-- Match expression: match expr with | pat => expr end
syntax "match " fnExpr " with" fnArm+ " end" : fnExpr

-- If-then-else expression: if cond then t else e
syntax "if " fnExpr " then " fnExpr " else " fnExpr : fnExpr
-- Inequality: expr ≠ expr
syntax fnExpr " ≠ " fnExpr : fnExpr

-- Let-in expression: let x := e1 ; e2
syntax "let " ident " := " fnExpr " ; " fnExpr : fnExpr
-- Option bind: let x ← e1 ; e2
syntax "let " ident " ← " fnExpr " ; " fnExpr : fnExpr

declare_syntax_cat fnStmt
syntax "let " ident " := " fnExpr : fnStmt
syntax "let " ident " ← " fnExpr : fnStmt

declare_syntax_cat fnPrecond
syntax ident "(" ident,+ ")" : fnPrecond

/-- Pattern-matching function. -/
syntax "defFn " ident "(" term ")" str
    fnParam* ("requires " fnPrecond,+)?
    ":" term " where" fnArm* : command

/-- Direct expression function (no pattern match). -/
syntax "defFn " ident "(" term ")" str
    fnParam* ("requires " fnPrecond,+)?
    ":" term " :=" fnExpr : command

/-- Imperative do-block function. -/
syntax "defFn " ident "(" term ")" str
    fnParam* ("requires " fnPrecond,+)?
    ":" term " begin" fnStmt*
    "return " fnExpr : command

-- ══════════════════════════════════════════════
-- Parsing helpers
-- ══════════════════════════════════════════════

mutual
partial def parsePatAtom
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPatAtom| _) => pure .wild
  | `(fnPatAtom| $n:ident) => pure (.var (toString n.getId))
  | `(fnPatAtom| $n:num) => pure (.natLit n.getNat)
  | `(fnPatAtom| [ ]) => pure .nil
  | `(fnPatAtom| [ $ps:fnPat,* ]) => do
    let parsed ← ps.getElems.mapM parsePat
    pure (parsed.foldr BodyPat.cons .nil)
  | `(fnPatAtom| ⟨ $args:fnPat,* ⟩) => do
    let a ← args.getElems.mapM parsePat
    pure (.ctor "⟨⟩" a.toList)
  | `(fnPatAtom| ( $p:fnPat )) => parsePat p
  | _ => Lean.Elab.throwUnsupportedSyntax

partial def parsePat
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPat| $a:fnPatAtom) => parsePatAtom a
  | `(fnPat| _) => pure .wild
  | `(fnPat| $n:ident) =>
    pure (.var (toString n.getId))
  | `(fnPat| .$n:ident $args:fnPatAtom*) => do
    let a ← args.mapM parsePatAtom
    pure (.ctor (toString n.getId) a.toList)
  | `(fnPat| $en:ident . $n:ident $args:fnPatAtom*) => do
    let a ← args.mapM parsePatAtom
    pure (.ctor s!"{en.getId}.{n.getId}" a.toList)
  | `(fnPat| ⟨$args:fnPat,*⟩) => do
    let a ← args.getElems.mapM parsePat
    pure (.ctor "⟨⟩" a.toList)
  | `(fnPat| ($p:fnPat)) => parsePat p
  | `(fnPat| $n:num) => pure (.natLit n.getNat)
  | `(fnPat| [ ]) => pure .nil
  | `(fnPat| [ $ps:fnPat,* ]) => do
    let parsed ← ps.getElems.mapM parsePat
    pure (parsed.foldr BodyPat.cons .nil)
  | `(fnPat| $h:fnPat :: $t:fnPat) =>
    pure (.cons (← parsePat h) (← parsePat t))
  | _ => Lean.Elab.throwUnsupportedSyntax
end

partial def parseExpr
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyExpr := do
  match stx with
  | `(fnExpr| [ ]) => pure .emptyList
  | `(fnExpr| [ $es:fnExpr,* ]) => do
    let elems ← es.getElems.mapM parseExpr
    pure (elems.foldr BodyExpr.cons .emptyList)
  | `(fnExpr| $n:num) =>
    pure (.natLit n.getNat)
  | `(fnExpr| $n:ident) =>
    let name := toString n.getId
    match name with
    | "true" => pure .true_
    | "false" => pure .false_
    | _ => pure (.var name)
  | `(fnExpr| ($e:fnExpr)) => parseExpr e
  | `(fnExpr| $r:fnExpr · $m:ident) =>
    pure (.dot (← parseExpr r)
      (toString m.getId))
  | `(fnExpr| $r:fnExpr ·flatMap fun $p:ident =>
        $b:fnExpr) => do
    pure (.flatMap (← parseExpr r)
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
  | `(fnExpr| $e:fnExpr ! $i:fnExpr) =>
    pure (.indexBang (← parseExpr e) (← parseExpr i))
  | `(fnExpr| $fn:ident ‹ $args:fnExpr,* ›) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.call (toString fn.getId) as_.toList)
  | `(fnExpr| $e:fnExpr ·foldlM $fn:ident
        $init:fnExpr) =>
    pure (.foldlM (toString fn.getId)
      (← parseExpr init) (← parseExpr e))
  | `(fnExpr| $a:fnExpr < $b:fnExpr < $c:fnExpr) =>
    pure (.ltChain [← parseExpr a, ← parseExpr b,
      ← parseExpr c])
  | `(fnExpr| $l:fnExpr < $r:fnExpr) =>
    pure (.lt (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ≤ $r:fnExpr) =>
    pure (.le (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr + $r:fnExpr) =>
    pure (.add (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr - $r:fnExpr) =>
    pure (.sub (← parseExpr l) (← parseExpr r))
  | `(fnExpr| ∅) => pure .emptySet
  | `(fnExpr| ⦃ $e:fnExpr ⦄) =>
    pure (.setSingleton (← parseExpr e))
  | `(fnExpr| $l:fnExpr ∪ $r:fnExpr) =>
    pure (.setUnion (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $e:fnExpr ·setFlatMap fun $p:ident =>
        $b:fnExpr) => do
    pure (.setFlatMap (← parseExpr e)
      (toString p.getId) (← parseExpr b))
  | `(fnExpr| $e:fnExpr ·forAll fun $p:ident =>
        $b:fnExpr) => do
    pure (.setAll (← parseExpr e)
      (toString p.getId) (← parseExpr b))
  | `(fnExpr| $l:fnExpr ∧ $r:fnExpr) =>
    pure (.and (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ∨ $r:fnExpr) =>
    pure (.or (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr → $r:fnExpr) =>
    pure (.implies (← parseExpr l) (← parseExpr r))
  | `(fnExpr| ∀∀ $p:ident , $b:fnExpr) =>
    pure (.forall_ (toString p.getId) (← parseExpr b))
  | `(fnExpr| sorry) => pure .sorryProof
  | `(fnExpr| lean_proof($s:str)) =>
    pure (.leanProof s.getString)
  | `(fnExpr| match $scrut:fnExpr with
        $arms:fnArm* end) => do
    let scrutAst ← parseExpr scrut
    let parsedArms ← arms.mapM fun arm =>
      match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure ([← parsePat p], ← parseExpr rhs)
      | _ => Lean.Elab.throwUnsupportedSyntax
    pure (.match_ scrutAst parsedArms.toList)
  | `(fnExpr| let $n:ident := $v:fnExpr ; $b:fnExpr) => do
    pure (.letIn (toString n.getId)
      (← parseExpr v) (← parseExpr b))
  | `(fnExpr| let $n:ident ← $v:fnExpr ; $b:fnExpr) => do
    pure (.letBindIn (toString n.getId)
      (← parseExpr v) (← parseExpr b))
  | `(fnExpr| if $c:fnExpr then $t:fnExpr else $e:fnExpr) =>
    pure (.ifThenElse (← parseExpr c) (← parseExpr t)
      (← parseExpr e))
  | `(fnExpr| $l:fnExpr ≠ $r:fnExpr) =>
    pure (.neq (← parseExpr l) (← parseExpr r))
  | _ => Lean.Elab.throwUnsupportedSyntax

/-- Fold a sequence of `fnStmt` syntax nodes followed by a
    return expression into a chained `letIn`/`letBindIn`
    `BodyExpr`. -/
def parseStmtsAsExpr
    (stmts : Array Lean.Syntax) (ret : BodyExpr)
    : Lean.Elab.Command.CommandElabM BodyExpr := do
  let mut acc := ret
  for stx in stmts.reverse do
    match stx with
    | `(fnStmt| let $n:ident := $e:fnExpr) =>
      acc := .letIn (toString n.getId) (← parseExpr e) acc
    | `(fnStmt| let $n:ident ← $e:fnExpr) =>
      acc := .letBindIn (toString n.getId)
        (← parseExpr e) acc
    | _ => Lean.Elab.throwUnsupportedSyntax
  pure acc

def parseFnParam
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.TSyntax `str
         × Lean.Syntax) := do
  match stx with
  | `(fnParam| ($n:ident $d:str : $t:term)) =>
    pure (n, d, t)
  | _ => Lean.Elab.throwUnsupportedSyntax

def parsePrecond
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (String × List String) := do
  match stx with
  | `(fnPrecond| $n:ident ($args:ident,*)) =>
    pure (toString n.getId,
      args.getElems.toList.map
        (toString ·.getId))
  | _ => Lean.Elab.throwUnsupportedSyntax

-- ══════════════════════════════════════════════
-- Core elaboration helpers
-- ══════════════════════════════════════════════

/-- Normalise a Lean type string for def generation.
    Maps DSL-only types (e.g. `Set T`) to their Lean
    equivalents (e.g. `List T`). -/
private def normaliseLeanType (s : String) : String :=
  (DSLType.parse s).toLean

def buildFnType
    (paramData : Array (Lean.Ident × Lean.TSyntax `str
      × Lean.Syntax))
    (retTy : Lean.TSyntax `term)
    : Lean.Elab.Command.CommandElabM String := do
  let paramTypeStrs := paramData.map fun (_, _, pt) =>
    let raw := if pt.isIdent then toString pt.getId
      else pt.reprint.getD (toString pt)
    normaliseLeanType raw
  let retRepr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  pure (" → ".intercalate paramTypeStrs.toList
    ++ s!" → {normaliseLeanType retRepr}")

open Lean Elab Command in
def buildFnDef
    (name : Ident)
    (symDoc : TSyntax `term)
    (doc : TSyntax `str)
    (paramData : Array (Ident × TSyntax `str
      × Syntax))
    (retTy : TSyntax `term)
    (body : TSyntax `term)
    (preconds : List (String × List String) := [])
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
  let retStr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  let retTn ← `(DSLType.parse $(quote retStr))
  let paramList ← `([$[$paramDefs],*])
  let precondDefs ← preconds.mapM fun (pn, args) => do
    `({ name := $(quote pn),
        args := $(quote args) : Precondition })
  let precondList ← `([$[$precondDefs.toArray],*])
  let fnDefId := mkIdent (name.getId ++ `fnDef)
  elabCommand (← `(command|
    def $fnDefId : FnDef :=
      { name := $ns,
        symbolDoc := ($symDoc : Doc), doc := $doc,
        params := $paramList,
        returnType := $retTn,
        preconditions := $precondList,
        body := $body }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerFnDef $fnDefId $modName))

/-- Build precondition proof parameter strings for
    the generated Lean def. Each precondition
    `prop(a, b)` becomes `(h_prop : prop a b)`. -/
private def precondParamBinds
    (preconds : List (String × List String))
    : String :=
  " ".intercalate
    (preconds.map fun (pn, args) =>
      let argStr := " ".intercalate args
      s!"(h_{pn} : {pn} {argStr})")

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* $[requires $reqs:fnPrecond,*]?
       : $retTy:term where
       $arms:fnArm*) => do
    let paramData ← ps.mapM parseFnParam
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM
          (parsePrecond ·.raw)
      | none => pure []
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
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        let rhsStr := rhsAst.toLeanWith
          fnNameStr precondNames
        s!"  | {patStr} => {rhsStr}"
    let defKw := "def"
    let paramNames := paramData.toList.map
      fun (pn, _, _) => toString pn.getId
    let defStr ←
      if preconds.isEmpty then
        let tyStr ← buildFnType paramData retTy
        pure s!"{defKw} {name.getId} : {tyStr}\n\
          {"\n".intercalate armStrs}"
      else do
        let paramBinds := " ".intercalate
          (paramData.toList.map fun (pn, _, pt) =>
            let tyStr :=
              if pt.isIdent then toString pt.getId
              else pt.reprint.getD (toString pt)
            s!"({pn.getId} : {normaliseLeanType tyStr})")
        let precBinds := precondParamBinds preconds
        let retRaw :=
          if retTy.raw.isIdent
          then toString retTy.raw.getId
          else retTy.raw.reprint.getD (toString retTy)
        let retRepr := normaliseLeanType retRaw
        let matchArgs := ", ".intercalate paramNames
        pure s!"{defKw} {name.getId} \
          {paramBinds} {precBinds} : {retRepr} :=\n\
          match {matchArgs} with\n\
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
    buildFnDef name symDoc doc paramData retTy
      bodyTerm preconds

-- ══════════════════════════════════════════════
-- Direct expression form
-- ══════════════════════════════════════════════

open Lean Elab Command in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* $[requires $reqs:fnPrecond,*]?
       : $retTy:term := $rhs:fnExpr) => do
    let paramData ← ps.mapM parseFnParam
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM
          (parsePrecond ·.raw)
      | none => pure []
    let rhsAst ← parseExpr rhs
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let rhsStr := rhsAst.toLeanWith
      fnNameStr precondNames
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {normaliseLeanType tyStr})")
    let precBinds := precondParamBinds preconds
    let retRaw :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let retRepr := normaliseLeanType retRaw
    let defStr :=
      s!"def {name.getId} {paramBinds} \
         {precBinds} : {retRepr} :=\n  {rhsStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    let bodyTerm ←
      `(FnBody.expr $(quoteExpr rhsAst))
    buildFnDef name symDoc doc paramData retTy
      bodyTerm preconds

-- ══════════════════════════════════════════════
-- Do-block form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* $[requires $reqs:fnPrecond,*]?
       : $retTy:term begin
       $stmts:fnStmt* return $ret:fnExpr) => do
    let paramData ← ps.mapM parseFnParam
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM
          (parsePrecond ·.raw)
      | none => pure []
    let parsedRet ← parseExpr ret
    let rhsAst ← parseStmtsAsExpr stmts parsedRet
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let rhsStr := rhsAst.toLeanWith
      fnNameStr precondNames
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {normaliseLeanType tyStr})")
    let precBinds := precondParamBinds preconds
    let retRaw :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let retRepr := normaliseLeanType retRaw
    let defStr :=
      s!"def {name.getId} {paramBinds} \
         {precBinds} : {retRepr} :=\n  {rhsStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    let bodyTerm ←
      `(FnBody.expr $(quoteExpr rhsAst))
    buildFnDef name symDoc doc paramData retTy
      bodyTerm preconds
