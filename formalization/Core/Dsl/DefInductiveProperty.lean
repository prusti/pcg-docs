import Core.Registry
import Core.Dsl.DefFn
import Core.Dsl.Types.InductivePropertyDef
import Core.Export.Lean
import Lean

open Lean in

declare_syntax_cat inductivePropBinder

/-- A bound-variable group in an inductive-property rule:
    either a single unannotated name `{a}` or a typed group
    `{a b c : T}`. Multiple groups may appear. -/
syntax "{" ident,+ "}" : inductivePropBinder
syntax "{" ident,+ " : " term "}" : inductivePropBinder

declare_syntax_cat inductivePropRule

/-- One inference rule of an inductive property:

    ```
    | name {a} {b : T} … from (premise1, premise2, …) ⊢ conclusion
    ```

    Each `{…}` group introduces universally-quantified bound
    variables (rendered as `∀ {bvar*}` in Lean and as a
    side-condition label in the LaTeX inference rule).

    Premises are Lean terms whose source is preserved and
    rendered above the inference line. The conclusion is the
    predicate applied to its indices, also a Lean term. -/
syntax "| " ident
    inductivePropBinder*
    ("from " "(" term,+ ")")?
    "⊢ " term
    : inductivePropRule

/-- Define an inductive property exported to Lean (as an
    `inductive Name … : Prop`) and to the LaTeX presentation
    (as a sequence of `\inferrule` blocks, one per rule). The
    Rust exporter intentionally skips inductive properties
    because they are Prop-level and have no runtime payload.

    Example:
    ```
    defInductiveProperty HasNonDeepLeaf
        (.plain "h", .plain "HasNonDeepLeaf")
      "Has Non-Deep Leaf"
      (.plain "An init tree has a non-`.deep` descendant leaf.")
      (it : InitialisationTree)
    where
      | leaf {cap : InitialisationState}
          from (cap ≠ .deep)
          ⊢ HasNonDeepLeaf (.leaf cap)
      | fields {fs} {x}
          from (x ∈ fs, HasNonDeepLeaf x.2.2)
          ⊢ HasNonDeepLeaf (.internal (.fields fs))
    ``` -/
syntax "defInductiveProperty " ident ("{" ident+ "}")?
    "(" term "," term ")"
    str "(" term ")"
    fnParam* " where"
    inductivePropRule*
    : command

private def parseRuleBinder
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (List (String × Option String)) := do
  match stx with
  | `(inductivePropBinder| { $ns:ident,* }) =>
    pure (ns.getElems.toList.map fun n =>
      (toString n.getId, none))
  | `(inductivePropBinder|
        { $ns:ident,* : $t:term }) =>
    let typeStr :=
      if t.raw.isIdent then toString t.raw.getId
      else t.raw.reprint.getD (toString t.raw)
    let ty := typeStr.trimAscii.toString
    pure (ns.getElems.toList.map fun n =>
      (toString n.getId, some ty))
  | _ => Lean.Elab.throwUnsupportedSyntax

private def termToString
    (t : Lean.TSyntax `term) : String :=
  if t.raw.isIdent then toString t.raw.getId
  else (t.raw.reprint.getD (toString t.raw)).trimAscii.toString

private structure ParsedRule where
  name : Lean.Ident
  binders : List (String × Option String)
  premises : List (String × Lean.TSyntax `term)
  conclusion : String
  conclusionStx : Lean.TSyntax `term

private def parseInductivePropRule
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM ParsedRule := do
  match stx with
  | `(inductivePropRule|
        | $name:ident
          $bgroups:inductivePropBinder*
          $[from ( $prems:term,* )]?
          ⊢ $concl:term) =>
    let bgroupLists ←
      bgroups.toList.mapM fun b => parseRuleBinder b.raw
    let bs := bgroupLists.flatten
    let premList : List (Lean.TSyntax `term) :=
      match prems with
      | some sep => sep.getElems.toList
      | none => []
    let premPairs := premList.map fun p => (termToString p, p)
    pure
      { name := name
        binders := bs
        premises := premPairs
        conclusion := termToString concl
        conclusionStx := concl }
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defInductiveProperty $name:ident
        $[{ $tps:ident* }]?
        ($symDoc:term, $setDoc:term)
        $docParam:str ($doc:term)
        $ps:fnParam*
        where
        $rs:inductivePropRule*) => do
    let parsedRules ← rs.mapM
      (parseInductivePropRule ∘ TSyntax.raw)
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let paramData ← ps.mapM parseFnParam
    -- Build the `inductive` declaration as a string and reparse,
    -- since each rule's premises and conclusion are arbitrary
    -- Lean terms whose source we pass through verbatim.
    let tpStr := if typeParamNames.isEmpty then ""
      else " " ++ " ".intercalate
        (typeParamNames.map fun p => s!"({p} : Type)")
    let paramStr := paramData.toList.foldl
      (init := "") fun acc (pn, _, pt) =>
        let typeStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt) |>.trimAscii.toString
        acc ++ s!" ({pn.getId} : {typeStr})"
    let paramSig :=
      if paramData.isEmpty then " : Prop"
      else s!" :{paramStr} → Prop"
    let renderBinder : String × Option String → String
      | (n, none)   => "{" ++ n ++ "}"
      | (n, some t) => "{" ++ n ++ " : " ++ t ++ "}"
    let ctorStrs := parsedRules.toList.map fun r =>
      let bs := r.binders.map renderBinder
      let parts := r.premises.map (·.1) ++ [r.conclusion]
      let arrowChain := " → ".intercalate parts
      let typ := match bs with
        | [] => arrowChain
        | _ => "∀ " ++ " ".intercalate bs ++ ", " ++ arrowChain
      s!"  | {r.name.getId} : {typ}"
    let inductiveStr :=
      s!"inductive {name.getId}{tpStr}{paramSig} where\n"
        ++ String.intercalate "\n" ctorStrs
    let env ← getEnv
    match Parser.runParserCategory env `command inductiveStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defInductiveProperty: parse error: {e}\n\
        ---\n{inductiveStr}\n---"
    -- Build the InductivePropertyDef registry term.
    let paramDefs ← paramData.mapM fun (pn, pd, pt) => do
      let an : TSyntax `term := quote (toString pn.getId)
      let typeStr :=
        if pt.isIdent then toString pt.getId
        else pt.reprint.getD (toString pt) |>.trimAscii.toString
      let tnTerm : TSyntax `term := quote typeStr
      `({ name := $an,
          ty := DSLType.parse $tnTerm,
          doc := ($pd : Doc) : FieldDef })
    let paramList ← `([$[$paramDefs],*])
    let ruleDefs : Array (TSyntax `term)
      ← parsedRules.mapM fun r => do
      let nameStr : TSyntax `term := quote (toString r.name.getId)
      let binderTerms : Array (TSyntax `term) ←
        r.binders.toArray.mapM fun (bn, bt) => do
          let bnStr : TSyntax `term := quote bn
          match bt with
          | none =>
            `({ name := $bnStr, type := none
                : InductiveRuleBinder })
          | some t =>
            let tStr : TSyntax `term := quote t
            `({ name := $bnStr, type := some $tStr
                : InductiveRuleBinder })
      let bindersTerm ← `([$[$binderTerms],*])
      let premStrs := r.premises.map (·.1)
      let premTerms : Array (TSyntax `term) :=
        premStrs.toArray.map fun s => quote s
      let premsTerm ← `([$[$premTerms],*])
      let conclusionTerm : TSyntax `term := quote r.conclusion
      `({ name := $nameStr,
          binders := $bindersTerm,
          premises := $premsTerm,
          conclusion := $conclusionTerm
          : InductiveRule })
    let rulesTerm ← `([$[$ruleDefs],*])
    let nameStr : TSyntax `term := quote (toString name.getId)
    let typeParamsTerm : TSyntax `term := quote typeParamNames
    let leanSourceTerm : TSyntax `term := quote inductiveStr
    let ipDefId := mkIdent (name.getId ++ `inductivePropertyDef)
    elabCommand (← `(command|
      def $ipDefId : InductivePropertyDef :=
        { name := $nameStr,
          symbolDoc := ($symDoc : MathDoc),
          setDoc := ($setDoc : MathDoc),
          docParam := $docParam,
          doc := ($doc : Doc),
          typeParams := $typeParamsTerm,
          params := $paramList,
          rules := $rulesTerm,
          leanSource := $leanSourceTerm }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerInductivePropertyDef $ipDefId $modName))
