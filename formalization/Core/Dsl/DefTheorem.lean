import Core.Dsl.DefFn
import Core.Dsl.IdentRefs
import Core.Registry

open Core.Dsl.IdentRefs

/-! # `defTheorem`: register a DSL-level theorem

`defTheorem` records a propositional statement (built from a
`DslExpr`) together with the Lean identifier of an existing
proof. Two things are emitted:

1. A Lean `theorem` whose statement is the DSL expression
   lowered to a Lean `Prop` and whose proof is a direct
   reference to the supplied identifier. The Lean compiler
   then typechecks that the named term actually proves the
   stated proposition — keeping the LaTeX statement and the
   Lean-side proof in lock-step.
2. A `RegisteredTheorem` entry for the presentation exporter,
   which renders the theorem as a `\begin{theorem} … \end{theorem}`
   block followed by a `\begin{proof}` block reading
   "Proved in `<proofIdent>`".

## Syntax

```
defTheorem <name>
  (<displayDoc>)
  := <fnExpr — the theorem statement as a DslExpr>
  proof <proofIdent>
```

The `<displayDoc>` is a `Doc` term (typically a `.plain "..."`
or a `doc!"..."`) that appears as prose under the theorem
heading. The `<fnExpr>` parses with the same grammar as
`defProperty` bodies, so universal quantifiers (`∀∀ pr ∈
Program . …`), implication chains, and DSL applications all
work. The `<proofIdent>` is the Lean identifier of an
existing `theorem`/`def` whose type matches the lowered
statement. -/

/-- Top-level `defTheorem` command. -/
syntax "defTheorem " ident "(" term ")"
    ":=" fnExpr
    "proof " ident
    : command

open Lean Elab Command Term in
elab_rules : command
  | `(defTheorem $name:ident ($doc:term) :=
        $stmt:fnExpr proof $proofIdent:ident) => do
    clearAllParseBuffers
    let stmtAst ← parseExpr stmt
    -- Lower the statement to a Lean type expression with
    -- antecedent binders rebound (so `proof[h_…]`
    -- references inside the statement resolve to real
    -- hypotheses if the DSL expression contains them).
    -- `withProofMarkers := true` wraps each `proof[…]` body
    -- in a `dslProofMarker` placeholder so the in-tree
    -- elaborator below can graft the user-source syntax back
    -- in for InfoView positioning.
    let leanType := toString
      ((stmtAst.bindAntecedentNames
          (withProofMarkers := true)).toLeanASTWith ""
        [] [] (withProofMarkers := true))
    let proofName := toString proofIdent.getId
    let nameStr := toString name.getId
    -- Emit the in-tree Lean theorem so the source build
    -- typechecks the proof against the stated type.
    let env ← getEnv
    let cmdStr := s!"theorem {nameStr} : {leanType} := \
      @{proofName}"
    match Parser.runParserCategory env `command cmdStr with
    | .ok stx =>
      let userProofs ← takeProofSyntaxes
      let (stx, _) := graftDslProofMarkers userProofs stx
      let stx ← graftLocalIdentsFromBuffers stx
      elabCommand stx
    | .error e =>
      drainAllParseBuffers
      throwError s!"defTheorem: parse error: {e}\n\
        ---\n{cmdStr}\n---"
    setUserDeclRanges name (← getRef)
    -- Build a `TheoremDef` value and register it for the
    -- presentation exporter.
    let nameTerm : TSyntax `term := quote nameStr
    let proofTerm : TSyntax `term := quote proofName
    let stmtTerm : TSyntax `term := quote stmtAst
    let tdId : Ident := mkIdent (name.getId ++ `theoremDef)
    elabCommand (← `(command|
      def $tdId : TheoremDef :=
        { name := $nameTerm,
          doc := ($doc : Doc),
          statement := $stmtTerm,
          proofIdent := $proofTerm }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerTheoremDef $tdId $modName))
    flushIdentRefs
