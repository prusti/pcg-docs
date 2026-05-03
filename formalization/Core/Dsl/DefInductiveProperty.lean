import Core.Registry
import Core.Dsl.DefFn
import Core.Dsl.ElabUtils
import Core.Dsl.IdentRefs
import Core.Dsl.Types.InductivePropertyDef
import Core.Export.Lean
import Lean

open Core.Dsl.IdentRefs

open Core.Dsl.ElabUtils

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

    Premises and the conclusion are DSL `fnExpr` expressions
    — structured DSL terms — so the LaTeX renderer can
    hyperlink constructor/function references and use math
    notation for operators. -/
syntax "| " ident
    inductivePropBinder*
    ("from " "(" fnExpr,+ ")")?
    "⊢ " fnExpr
    : inductivePropRule

/-- Define an inductive property exported to Lean (as an
    `inductive Name … : Prop`) and to the LaTeX presentation
    (as a sequence of `\inferrule` blocks, one per rule). The
    Rust exporter intentionally skips inductive properties
    because they are Prop-level and have no runtime payload.

    Example:
    ```
    defInductiveProperty HasNonDeepLeaf
      "Has Non-Deep Leaf"
      (.plain "An init tree has a non-`.deep` descendant leaf.")
      (it : InitTree)
    where
      | leaf {cap : InitialisationState}
          from (cap ≠ .deep)
          ⊢ HasNonDeepLeaf (.leaf cap)
      | fields {fs} {x}
          from (x ∈ fs, HasNonDeepLeaf x.2.2)
          ⊢ HasNonDeepLeaf (.internal (.fields fs))
    ``` -/
syntax "defInductiveProperty " ident ("{" ident+ "}")?
    str "(" term ")"
    fnParam* ("displayed " term)? " where"
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
    let ty := toTypeStrTrimmed t.raw
    pure (ns.getElems.toList.map fun n =>
      (toString n.getId, some ty))
  | _ => Lean.Elab.throwUnsupportedSyntax

private structure ParsedRule where
  name : Lean.Ident
  binders : List (String × Option String)
  /-- Each premise is both its DSL `DslExpr` (for LaTeX and
      registry purposes) and its Lean source (for emission
      into the `inductive … where | …` declaration). -/
  premises : List (DslExpr × String)
  /-- Conclusion as a DSL expression paired with its Lean
      source form. -/
  conclusion : DslExpr × String

/-- Convert a parsed `DslExpr` to a Lean-source string using
    `DslExpr.toLean`, which the defInductiveProperty command
    splices into the generated `inductive … where | …`
    declaration. -/
private def dslExprToLeanStr (e : DslExpr) : String :=
  e.toLeanWith "" []

private def parseInductivePropRule
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM ParsedRule := do
  match stx with
  | `(inductivePropRule|
        | $name:ident
          $bgroups:inductivePropBinder*
          $[from ( $prems:fnExpr,* )]?
          ⊢ $concl:fnExpr) =>
    let bgroupLists ←
      bgroups.toList.mapM fun b => parseRuleBinder b.raw
    let bs := bgroupLists.flatten
    let premList : List (Lean.TSyntax `fnExpr) :=
      match prems with
      | some sep => sep.getElems.toList
      | none => []
    let premAsts ← premList.mapM (parseExpr ·.raw)
    let concAst ← parseExpr concl.raw
    let premPairs := premAsts.map
      fun a => (a, dslExprToLeanStr a)
    pure
      { name := name
        binders := bs
        premises := premPairs
        conclusion := (concAst, dslExprToLeanStr concAst) }
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defInductiveProperty $name:ident
        $[{ $tps:ident* }]?
        $docParam:str ($doc:term)
        $ps:fnParam*
        $[displayed $dispDoc:term]?
        where
        $rs:inductivePropRule*) => do
    DslLint.lintDocTerm doc
    clearAllParseBuffers
    let parsedRules ← rs.mapM
      (parseInductivePropRule ∘ TSyntax.raw)
    let typeParamNames : List String := typeParamNames tps
    let paramData ← ps.mapM parseFnParam
    for (_, _, ty) in paramData do recordTypeIdents ty
    -- The `displayed` template is a single `Doc` value
    -- (typically `doc! "$...$"`). At runtime we convert it to
    -- a `List DisplayPart` via `Doc.toDisplayParts`, with the
    -- registered parameter names so each `MathDoc.text name`
    -- (i.e. each `#name` reference inside the `doc!`'s math
    -- block) becomes a parameter slot. Doing the conversion
    -- in the generated `InductivePropertyDef` term — rather
    -- than at macro-expansion time — keeps the `displayed`
    -- syntax open to any `Doc`-producing expression, not just
    -- a literal `doc!` invocation.
    let paramNamesTerm : TSyntax `term :=
      quote (paramData.toList.map fun (pn, _, _) =>
        toString pn.getId)
    let displayTerm : TSyntax `term ← match dispDoc with
      | some d =>
        `((some
            (Doc.toDisplayParts $paramNamesTerm
              ($d : Doc))
            : Option (List DisplayPart)))
      | none => `((none : Option (List DisplayPart)))
    -- Build the `inductive` declaration as a string and reparse,
    -- since each rule's premises and conclusion are arbitrary
    -- Lean terms whose source we pass through verbatim.
    let tpStr := renderTypeParamSig typeParamNames
    let paramItems := paramData.toList.map
      fun (pn, _, pt) =>
        s!"({pn.getId} : {toTypeStrTrimmed pt})"
    let paramSig :=
      if paramItems.isEmpty then " : Prop"
      else s!" : {" → ".intercalate paramItems} → Prop"
    let renderBinder : String × Option String → String
      | (n, none)   => "{" ++ n ++ "}"
      | (n, some t) => "{" ++ n ++ " : " ++ t ++ "}"
    let ctorStrs := parsedRules.toList.map fun r =>
      let bs := r.binders.map renderBinder
      let parts := r.premises.map (·.2) ++ [r.conclusion.2]
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
    | .ok stx =>
      let stx := graftUserNameToken name.getId name.raw stx
      elabCommand stx
    | .error e =>
      throwError s!"defInductiveProperty: parse error: {e}\n\
        ---\n{inductiveStr}\n---"
    setUserDeclRanges name (← getRef)
    -- Build the InductivePropertyDef registry term.
    let paramDefs ← paramData.mapM fun (pn, pd, pt) => do
      let an : TSyntax `term := quote (toString pn.getId)
      let tnTerm : TSyntax `term := quote (toTypeStrTrimmed pt)
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
      let premExprs := r.premises.map (·.1)
      let premTerms : Array (TSyntax `term) :=
        premExprs.toArray.map fun e => quote e
      let premsTerm ← `([$[$premTerms],*])
      let conclusionTerm : TSyntax `term := quote r.conclusion.1
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
          docParam := $docParam,
          doc := ($doc : Doc),
          typeParams := $typeParamsTerm,
          params := $paramList,
          rules := $rulesTerm,
          display := $displayTerm,
          leanSource := $leanSourceTerm }))
    registerInCurrentModule ``registerInductivePropertyDef ipDefId
    flushIdentRefs
