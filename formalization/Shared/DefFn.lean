import Shared.Registry
import Lean

open Lean in

declare_syntax_cat fnParam
syntax "(" ident str ":" term ")" : fnParam

declare_syntax_cat fnPat
syntax "_" : fnPat
syntax ident : fnPat
syntax "." ident fnPat* : fnPat

declare_syntax_cat fnExpr
syntax "[" "]" : fnExpr
syntax ident : fnExpr
syntax "(" fnExpr ")" : fnExpr
syntax ident "·" ident : fnExpr
syntax ident "·flatMap" "fun" ident "=>" fnExpr : fnExpr
syntax fnExpr " :: " fnExpr : fnExpr
syntax fnExpr " ++ " fnExpr : fnExpr

declare_syntax_cat fnArm
syntax "| " fnPat+ " => " fnExpr : fnArm

/-- Define a function with cross-language export.
    Body uses a restricted match-arm language.
    Use `x·method` for dot notation, `x·flatMap fun a => b`
    for higher-order calls. -/
syntax "defFn " ident "(" term ")" str
    fnParam* ":" term " where" fnArm* : command

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
  | _ => Lean.Elab.throwUnsupportedSyntax

private partial def parseExpr
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyExpr := do
  match stx with
  | `(fnExpr| [ ]) => pure .emptyList
  | `(fnExpr| $n:ident) =>
    pure (.var (toString n.getId))
  | `(fnExpr| ($e:fnExpr)) => parseExpr e
  | `(fnExpr| $r:ident · $m:ident) =>
    pure (.dot (.var (toString r.getId))
      (toString m.getId))
  | `(fnExpr| $r:ident ·flatMap fun $p:ident =>
        $b:fnExpr) => do
    let bd ← parseExpr b
    pure (.flatMap (.var (toString r.getId))
      (toString p.getId) bd)
  | `(fnExpr| $h:fnExpr :: $t:fnExpr) =>
    pure (.cons (← parseExpr h) (← parseExpr t))
  | `(fnExpr| $l:fnExpr ++ $r:fnExpr) =>
    pure (.append (← parseExpr l) (← parseExpr r))
  | _ => Lean.Elab.throwUnsupportedSyntax

private partial def exprToTerm
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  match stx with
  | `(fnExpr| [ ]) => `([])
  | `(fnExpr| $n:ident) => pure n
  | `(fnExpr| ($e:fnExpr)) => exprToTerm e
  | `(fnExpr| $r:ident · $m:ident) =>
    `($r |>.$(Lean.mkIdent m.getId))
  | `(fnExpr| $r:ident ·flatMap fun $p:ident =>
        $b:fnExpr) => do
    let bd ← exprToTerm b
    `($r |>.flatMap fun $p => $bd)
  | `(fnExpr| $h:fnExpr :: $t:fnExpr) => do
    `($(← exprToTerm h) :: $(← exprToTerm t))
  | `(fnExpr| $l:fnExpr ++ $r:fnExpr) => do
    `($(← exprToTerm l) ++ $(← exprToTerm r))
  | _ => Lean.Elab.throwUnsupportedSyntax

private partial def patToTerm
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  match stx with
  | `(fnPat| _) => `(_)
  | `(fnPat| $n:ident) => pure n
  | `(fnPat| .$n:ident $args:fnPat*) => do
    let ts ← args.mapM patToTerm
    let si := Lean.SourceInfo.none
    let dotIdent := Lean.Syntax.node si
      ``Lean.Parser.Term.dotIdent
      #[Lean.Syntax.atom si ".",
        Lean.mkIdent n.getId]
    let base : Lean.TSyntax `term := ⟨dotIdent⟩
    pure (ts.foldl
      (fun acc a => Lean.Syntax.mkApp acc #[a]) base)
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

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) $doc:str
       $ps:fnParam* : $retTy:term where
       $arms:fnArm*) => do
    let paramData ← ps.mapM parseFnParam
    let parsed ← arms.mapM fun arm => match arm with
      | `(fnArm| | $pats:fnPat* => $rhs:fnExpr) => do
        let patAst ← pats.mapM parsePat
        let rhsAst ← parseExpr rhs
        let lPats ← pats.mapM patToTerm
        let lRhs ← exprToTerm rhs
        pure (patAst.toList, rhsAst, lPats, lRhs)
      | _ => throwError "invalid fnArm"
    -- Build function type
    let fnTy ← paramData.foldrM
      (fun (_, _, pty) (acc : TSyntax `term) => do
        let pt : TSyntax `term := ⟨pty⟩
        `($pt → $acc))
      retTy
    -- Build the Lean def by rendering from the AST.
    let paramTypeStrs := paramData.map fun (_, _, pt) =>
      if pt.isIdent then toString pt.getId
      else pt.reprint.getD (toString pt)
    let retRepr :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let tyStr := " → ".intercalate
      paramTypeStrs.toList ++ s!" → {retRepr}"
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst, _, _) =>
        let patStr := " ".intercalate
          (patAst.map BodyPat.toLean)
        s!"  | {patStr} => {rhsAst.toLean}"
    let defStr := s!"def {name.getId} : {tyStr}\n\
      {"\n".intercalate armStrs}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    -- Build FnDef metadata
    let paramDefs ← paramData.mapM
      fun (pn, pd, pt) => do
        let ns : TSyntax `term :=
          quote (toString pn.getId)
        let typeStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        let tn : TSyntax `term := quote typeStr
        `({ name := $ns, typeName := $tn,
            doc := $pd : FieldDef })
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst, _, _) => do
        let pq : TSyntax `term := quote patAst
        let rq : TSyntax `term := quoteExpr rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let ns : TSyntax `term :=
      quote (toString name.getId)
    let retStr :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let retTn : TSyntax `term := quote retStr
    let paramList ← `([$[$paramDefs],*])
    let armList ← `([$[$armDefs],*])
    elabCommand (← `(command|
      def $(mkIdent (name.getId ++ `fnDef)) : FnDef :=
        { name := $ns,
          symbolDoc := ($symDoc : Doc), doc := $doc,
          params := $paramList,
          returnType := $retTn,
          body := $armList }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    let fnDefId := mkIdent (name.getId ++ `fnDef)
    elabCommand (← `(command|
      initialize registerFnDef $fnDefId $modName))
