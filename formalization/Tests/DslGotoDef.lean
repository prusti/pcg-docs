import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefAlias
import Core.Dsl.DefStruct
import Core.Dsl.IdentRefs
import OpSem.Program
import OpSem.StackFrame
import PCG.Owned.OwnedState
import Lean

open Core.Dsl.IdentRefs

/-!
# Build-time checks: gotoDef points at the DSL source

Each DSL command (`defFn`, `defProperty`, `defAlias`,
`defInductiveProperty`) elaborates by rendering its body to a
string and re-parsing it, which would otherwise leave the
recorded `DeclarationRanges` pointing at the start of the file
(synthetic positions in the rendered string). After
elaboration, `Core.Dsl.IdentRefs.setUserDeclRanges` re-registers
each declaration's ranges using the original DSL syntax.

The `run_cmd` blocks below define a sample DSL declaration and
then assert that the registered range starts on a line strictly
after the declaration's import preamble. If the override is
missing the recorded range collapses to line 1 and the assert
fails the build. -/

namespace Tests.DslGotoDef

defAlias TestAliasDecl (.text "tα", .text "TestAliasDecl")
  "Test Alias"
  (.plain "Sample type alias.")
  := Nat

run_cmd do
  let some ranges ← Lean.findDeclarationRanges?
    ``Tests.DslGotoDef.TestAliasDecl
    | throwError "TestAliasDecl: no DeclarationRanges registered"
  let line := ranges.range.pos.line
  unless line > 1 do
    throwError s!"TestAliasDecl: range collapsed to line {line} \
      (expected the line of `defAlias TestAliasDecl ...`)"

defProperty testPropertyDecl (.plain "testPropertyDecl")
  short
    (.seq [.plain "test about ", x])
  long
    (.seq [.plain "test about ", x])
  (x "Test param." : Nat)
  := x < 10

run_cmd do
  let some ranges ← Lean.findDeclarationRanges?
    ``Tests.DslGotoDef.testPropertyDecl
    | throwError "testPropertyDecl: no DeclarationRanges registered"
  let line := ranges.range.pos.line
  unless line > 1 do
    throwError s!"testPropertyDecl: range collapsed to line {line} \
      (expected the line of `defProperty testPropertyDecl ...`)"

defFn testFnDecl (.plain "testFnDecl")
  (.plain "Sample defFn for the goto-def regression test.")
  (n "Test param." : Nat)
  : Nat :=
    n + 1

run_cmd do
  let some ranges ← Lean.findDeclarationRanges?
    ``Tests.DslGotoDef.testFnDecl
    | throwError "testFnDecl: no DeclarationRanges registered"
  let line := ranges.range.pos.line
  unless line > 1 do
    throwError s!"testFnDecl: range collapsed to line {line} \
      (expected the line of `defFn testFnDecl ...`)"

defInductiveProperty TestInductiveProp
  "Test Inductive Property"
  (.plain "Sample inductive property for the goto-def regression test.")
  (n "Test param." : Nat)
where
  | refl {x : Nat} ⊢ TestInductiveProp x

run_cmd do
  let some ranges ← Lean.findDeclarationRanges?
    ``Tests.DslGotoDef.TestInductiveProp
    | throwError
        "TestInductiveProp: no DeclarationRanges registered"
  let line := ranges.range.pos.line
  unless line > 1 do
    throwError s!"TestInductiveProp: range collapsed to line {line} \
      (expected the line of `defInductiveProperty TestInductiveProp ...`)"

-- Call-site gotoDef regression test. `flushIdentRefs` should
-- attach a `TermInfo` leaf to each user-source identifier in
-- a `defFn` body whose name resolves to a global constant,
-- so LSP gotoDef from the call site lands on the callee's
-- `defFn`. We verify by elaborating a synthesised `defFn`
-- caller under our own `withInfoTreeContext`, capturing the
-- resulting info trees, and walking them for a `TermInfo`
-- whose expression is a `const` reference to the expected
-- callee.
namespace Wrap

defFn testCallee (.plain "testCallee")
  (.plain "Callee for the call-site goto-def regression test.")
  : Nat := 1

defFn testGuard (.plain "testGuard")
  (.plain "Guard predicate for the call-site goto-def \
    regression test.")
  (n "Test param." : Nat)
  : Prop := n < 10

end Wrap

open Lean Elab Command in
/-- Run `defFn`-style command `src` and check that an
    elaborated `TermInfo` pointing at `target` appears
    somewhere in the resulting info trees — i.e. that
    `flushIdentRefs` attached a goto-def leaf for it. -/
private def checkCallSiteGotoDef
    (src : String) (target : Name) : CommandElabM Unit := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `command src with
    | .ok stx => pure stx
    | .error e => throwError s!"parse error in synthesised \
        defFn:\n---\n{src}\n---\n{e}"
  let pred : Lean.Elab.Info → Bool := fun info =>
    match info with
    | .ofTermInfo ti =>
      match ti.expr with
      | .const n _ => n == target
      | _ => false
    | _ => false
  let foundRef ← IO.mkRef false
  withInfoTreeContext (mkInfoTree := fun trees => do
      if trees.any (fun t => (t.findInfo? pred).isSome) then
        foundRef.set true
      return InfoTree.node
        (Info.ofCommandInfo
          { elaborator := `checkCallSiteGotoDef, stx })
        trees) do
    elabCommand stx
  let found ← foundRef.get
  if !found then
    throwError s!"call-site gotoDef regression: no TermInfo \
      pointing at {target} found in the info trees produced \
      by\n---\n{src}\n---\n\
      `flushIdentRefs` is not attaching the callee's resolved \
      const to the user-source token."

elab "checkCallSiteGotoDef" : command => do
  -- Direct expression body: `testCaller := testCallee`.
  checkCallSiteGotoDef
    "defFn testCallerSimple (.plain \"testCallerSimple\") \
       (.plain \"Simple direct caller.\") \
       : Nat := testCallee"
    `Tests.DslGotoDef.Wrap.testCallee
  -- Body uses a `let`-chain ending in the call site, mirroring
  -- `initialMachine`'s structure. Exercises the let-binding
  -- traversal in `parseExpr`.
  checkCallSiteGotoDef
    "defFn testCallerLet (.plain \"testCallerLet\") \
       (.plain \"Caller using a let-chain ending in a call.\") \
       : Nat := \
         let x := 1 ; \
         let y := 2 ; \
         testCallee"
    `Tests.DslGotoDef.Wrap.testCallee
  -- Body uses `requires` precondition and a let-chain ending
  -- in the call, fully mirroring `initialMachine`'s shape.
  checkCallSiteGotoDef
    "defFn testCallerReq (.plain \"testCallerReq\") \
       (.plain \"Caller with a precondition + let-chain.\") \
       (n \"Test param.\" : Nat) \
       requires testGuard n \
       : Nat := \
         let x := 1 ; \
         testCallee"
    `Tests.DslGotoDef.Wrap.testCallee
  -- defProperty body referencing a callee. Mirrors the way
  -- `FramingInvariant`'s body references `hasAllocation`,
  -- `hasCapability`, `Runnable`, etc. via `‹...›` calls.
  checkCallSiteGotoDef
    "defProperty testPropCallerSimple \
       (.plain \"testPropCallerSimple\") \
       short (.seq [.plain \"short\"]) \
       long (.seq [.plain \"long\"]) \
       (n \"Test param.\" : Nat) \
       := testGuard n"
    `Tests.DslGotoDef.Wrap.testGuard
  -- defProperty body using a forall + chained conjunctions
  -- ending with the call, the shape used by `FramingInvariant`.
  checkCallSiteGotoDef
    "defProperty testPropCallerForall \
       (.plain \"testPropCallerForall\") \
       short (.seq [.plain \"short\"]) \
       long (.seq [.plain \"long\"]) \
       := ∀∀ n ∈ Nat . \
            ‹break› n < 10 ∧ \
            ‹break› testGuard n"
    `Tests.DslGotoDef.Wrap.testGuard
  -- Same shape, but with the `‹break›` placed *before* the
  -- operator rather than the next conjunct. Exercises the
  -- `‹break›∧` and `‹break›→` parser rules.
  checkCallSiteGotoDef
    "defProperty testPropBreakBeforeOp \
       (.plain \"testPropBreakBeforeOp\") \
       short (.seq [.plain \"short\"]) \
       long (.seq [.plain \"long\"]) \
       := ∀∀ n ∈ Nat . \
            n < 10 ‹break›∧ \
            testGuard n \
            ‹break›→ testGuard (n + 1)"
    `Tests.DslGotoDef.Wrap.testGuard

namespace Wrap
checkCallSiteGotoDef
end Wrap

-- ══════════════════════════════════════════════
-- Build-time check: `proof[…]` InfoView positioning
-- ══════════════════════════════════════════════
--
-- Each `defFn`/`defProperty`/`defTheorem` body that uses
-- `proof[term]` must, after the in-tree DSL elaboration of
-- the synthesized `def`, carry a `TermInfo` whose source
-- range falls inside the *original user-source* `proof[…]`
-- body, not at synthetic positions inside the parsed-from-
-- string copy. Without this, the LSP InfoView is silent when
-- the cursor sits inside `proof[…]`.
--
-- The pipeline that gives us this is:
--   1. `parseExpr` on `proof[$t:term]` records `t.raw` into
--      `proofSyntaxBuffer`.
--   2. `toLeanASTAlg` with `withProofMarkers := true` wraps
--      each `.leanProof` rendering in a
--      `Core.Dsl.IdentRefs.dslProofMarker (…)` call.
--   3. After parsing the synthesized Lean source,
--      `graftDslProofMarkers` replaces each marker
--      application with the buffered user-source syntax.
--   4. The elaborator processes the grafted syntax and emits
--      `TermInfo` leaves at the user-source ranges.
--
-- This test elaborates a synthetic `defFn` whose body is
-- `Wrap.testReqCallee n proof[h_testGuard]` and verifies
-- that after elaboration there is a `TermInfo` whose
-- `stx.getPos?` falls inside the source range of the
-- `h_testGuard` identifier in the synthesized source.
namespace Wrap

defFn testReqCallee (.plain "testReqCallee")
  (.plain "Callee with a precondition for the proof[…] \
    InfoView regression test.")
  (n "Test param." : Nat)
  requires testGuard n
  : Nat := 0

end Wrap

/-- Walk a parsed `defFn`/`defProperty` syntax tree and
    return the first `Lean.Syntax.ident` whose name matches
    `needle`. Used by `checkProofInfoViewPosition` to locate
    the user-source position of a `proof[…]` body identifier
    in the test fixture. -/
private partial def findUserIdent
    (needle : Lean.Name) (stx : Lean.Syntax) : Option Lean.Syntax :=
  match stx with
  | .ident _ _ n _ => if n == needle then some stx else none
  | .node _ _ args =>
    args.foldl
      (fun acc child => acc.orElse (fun _ => findUserIdent needle child))
      none
  | _ => none

/-- Walk a parsed syntax tree and collect every
    `Lean.Syntax.ident` whose name matches `needle`, in
    depth-first / left-to-right order. Used by the local-
    ident gotoDef tests to locate a *usage* of a binder (the
    second occurrence — first is the binder itself). -/
private partial def collectUserIdents
    (needle : Lean.Name) (stx : Lean.Syntax) : Array Lean.Syntax :=
  match stx with
  | .ident _ _ n _ => if n == needle then #[stx] else #[]
  | .node _ _ args =>
    args.foldl
      (fun acc child => acc ++ collectUserIdents needle child)
      #[]
  | _ => #[]

open Lean Elab Command in
/-- Run `defFn`-style command `src` whose body is expected to
    contain a single `proof[…]` block, and check that after
    elaboration there's a `TermInfo` whose `stx` is the bare
    identifier `needleName` at the *exact* user-source
    position the parser recorded for the `proof[…]` body.
    Without the marker+graft pipeline, the `h_…` identifier
    in the parsed-from-string copy of the rendered Lean
    source carries a different (synthetic-relative-to-the-
    rendered-string) byte offset, so the test fails. -/
private def checkProofInfoViewPosition
    (src : String) (needleName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `command src with
    | .ok stx => pure stx
    | .error e => throwError s!"parse error in synthesised \
        defFn:\n---\n{src}\n---\n{e}"
  let some userIdent := findUserIdent needleName stx
    | throwError s!"checkProofInfoViewPosition: identifier \
        '{needleName}' not found in parsed src"
  let some userPos := userIdent.getPos?
    | throwError s!"checkProofInfoViewPosition: parsed \
        identifier '{needleName}' has no source position"
  let foundRef ← IO.mkRef false
  -- Walk every info-tree leaf produced during elaboration
  -- and look for a `TermInfo` whose `stx` matches the user-
  -- source identifier exactly (same position byte offset).
  -- The marker+graft pipeline must produce TermInfos whose
  -- positions echo the user's parse, so the LSP InfoView
  -- fires at the cursor sitting inside `proof[…]`.
  let pred : Lean.Elab.Info → Bool := fun info =>
    match info with
    | .ofTermInfo ti =>
      ti.stx.getKind == Lean.identKind &&
      ti.stx.getId == needleName &&
      (match ti.stx.getPos? with
        | some p => p.byteIdx == userPos.byteIdx
        | none => false)
    | _ => false
  withInfoTreeContext (mkInfoTree := fun trees => do
      if trees.any (fun t => (t.findInfo? pred).isSome) then
        foundRef.set true
      return InfoTree.node
        (Info.ofCommandInfo
          { elaborator := `checkProofInfoViewPosition, stx })
        trees) do
    elabCommand stx
  let found ← foundRef.get
  if !found then
    throwError s!"proof[…] InfoView regression: no TermInfo \
      with `original` source info found for identifier \
      '{needleName}' in:\n---\n{src}\n---\n\
      The marker+graft pipeline (parseExpr → \
      toLeanASTAlg(withProofMarkers) → graftDslProofMarkers) \
      is not preserving user-source positions for the proof \
      body, so the LSP InfoView would be silent at the \
      cursor."

elab "checkProofInfoViewPosition" : command => do
  -- Caller defFn: `n : Nat` in scope, `requires testGuard n`
  -- introduces `h_testGuard : testGuard n` as a precondition
  -- binder, and the body calls `Wrap.testReqCallee` whose own
  -- `requires testGuard(body's n)` slot consumes the proof.
  -- The user-source `h_testGuard` identifier inside
  -- `proof[h_testGuard]` is what `graftDslProofMarkers` must
  -- splice into the synthesized def, preserving its source
  -- range so a `TermInfo` lands inside it.
  checkProofInfoViewPosition
    "defFn testProofCaller (.plain \"testProofCaller\") \
       (.plain \"Caller exercising proof[…] graft.\") \
       (n \"Test param.\" : Nat) \
       requires testGuard n \
       : Nat := \
         Wrap.testReqCallee n proof[h_testGuard]"
    `h_testGuard
  -- defProperty body case: an implication chain whose
  -- bindAntecedentNames pass introduces an `h_testGuard`
  -- hypothesis that the goal references via `proof[…]`. This
  -- exercises the property path through `elabPropertyDecl`'s
  -- `graftDslProofMarkers` call, including the
  -- `bindAntecedentNames` interaction with marker rendering
  -- (the antecedent's stringification must preserve marker
  -- placeholders so the buffer ordering stays in sync).
  checkProofInfoViewPosition
    "defProperty testPropProofCaller \
       (.plain \"testPropProofCaller\") \
       short (.seq [.plain \"short\"]) \
       long (.seq [.plain \"long\"]) \
       (n \"Test param.\" : Nat) \
       := testGuard n → \
            Wrap.testReqCallee n proof[h_testGuard] = 0"
    `h_testGuard

namespace Wrap
checkProofInfoViewPosition
end Wrap

-- Smoke-test the struct-field registry via
-- `resolveStructField`: given a field name like
-- `"functions"`, it consults the `defStruct` registry and
-- returns the qualified Lean name(s) of every struct that
-- exposes that field. For names claimed by exactly one
-- struct (`functions` here), the list is a singleton.
--
-- Note: the production `↦` parser rule no longer calls
-- `resolveStructField` — field gotoDef now goes through
-- `recordStructFieldRef` + `graftLocalIdentsFromBuffers`,
-- so Lean's `Term.proj` elaborator picks the single
-- type-correct candidate from the receiver's type. The
-- end-to-end gotoDef behavior is checked by the
-- `checkFieldProjGotoDef` block below.
run_cmd do
  let resolved ← resolveStructField "functions"
  let expected : Lean.Name := `Program ++ `functions
  unless resolved == [expected] do
    throwError s!"resolveStructField resolved to {resolved}, \
      expected [{expected}]"

-- Smoke-test the ambiguous case: `locals` is claimed by at
-- least two registered structs (`OwnedState` and
-- `StackFrame`); the resolver should return both qualified
-- names rather than dropping the lookup.
run_cmd do
  let resolved ← resolveStructField "locals"
  let ownedStateLocals : Lean.Name := `OwnedState ++ `locals
  let stackFrameLocals : Lean.Name := `StackFrame ++ `locals
  unless resolved.contains ownedStateLocals
      ∧ resolved.contains stackFrameLocals do
    throwError s!"resolveStructField on `locals` returned \
      {resolved}; expected both {ownedStateLocals} and \
      {stackFrameLocals} in the list"

-- Field-projection regression: when a struct field name is
-- claimed by more than one struct (`id` is on both
-- `Provenance` and `RegionVid`), the parser must NOT emit a
-- `TermInfo` per candidate via `recordIdentRef`. Doing so
-- caused multi-target gotoDef from `prov ↦ id` to offer both
-- `Provenance.id` and `RegionVid.id` even though the receiver
-- is a `Provenance`. The fix routes the field token through
-- `recordStructFieldRef` (no `addConstInfo` per candidate);
-- Lean's own `Term.proj` elaborator then emits a single
-- type-correct `TermInfo` for `Provenance.id`.
--
-- For the graft to bite, the `.field` renderer in
-- `Core/LeanAST.lean` always parenthesises the receiver
-- (`(prov).id`) so Lean parses the projection as a
-- `Term.proj` node with `id` as a separate ident child. The
-- bare-dot form `prov.id` would parse to a single dotted
-- ident, leaving no child node for
-- `graftLocalIdentsFromBuffers` to splice the user-source
-- `id` syntax over — the user-position TermInfo would never
-- appear and LSP gotoDef would dead-end at the cursor.
--
-- The check below therefore asserts both:
--   1. some `TermInfo` mentions `Provenance.id` *at the
--      user-source byte offset* of the `id` token (the
--      type-correct projection grafted into the user's
--      source position); AND
--   2. no `TermInfo` mentions `RegionVid.id` (the
--      over-emission removed by the buffer change).
open Lean Elab Command in
/-- Walk a `Lean.Expr` and check whether `target`
    (a fully-qualified field-projector name like
    `Provenance.id`) appears as either a `const` reference
    (i.e. the projector applied as a function) or an anonymous
    `proj` whose struct name matches `target.getPrefix` (i.e.
    Lean elaborated the field access as a structure
    projection). Recurses into sub-terms. -/
private partial def exprMentions (target : Lean.Name) :
    Lean.Expr → Bool
  | .const n _ => n == target
  | .app f a => exprMentions target f || exprMentions target a
  | .proj sn _ s => sn == target.getPrefix || exprMentions target s
  | .mdata _ b => exprMentions target b
  | .lam _ t b _ =>
    exprMentions target t || exprMentions target b
  | .forallE _ t b _ =>
    exprMentions target t || exprMentions target b
  | .letE _ t v b _ =>
    exprMentions target t || exprMentions target v
      || exprMentions target b
  | _ => false

open Lean Elab Command in
/-- Run a `defFn` whose body is `prov ↦ id` (where `prov` is a
    `Provenance` parameter) and check that:
    1. some `TermInfo` produced during elaboration mentions
       `positiveTarget` (the type-correct projection)
       *at the user-source byte offset of `fieldNeedle`*.
       The byte-offset pin verifies that the `(recv).field`
       parenthesisation in the renderer + the struct-field
       graft in `graftLocalIdentsFromBuffers` successfully
       splice the user-source field token over the
       parsed-from-string copy, so LSP gotoDef on the user's
       `id` cursor lands on the type-correct constant.
    2. no `TermInfo` mentions `negativeTarget` (the
       over-emission the buffer change removed: previously
       the `↦` parser called `recordIdentRef` once per
       `resolveStructField` candidate, leaking a
       `RegionVid.id` `addConstInfo` leaf at the user
       position alongside the type-correct one). -/
private def checkFieldProjGotoDef
    (src : String) (positiveTarget negativeTarget : Name)
    (fieldNeedle : Name)
    : CommandElabM Unit := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `command src with
    | .ok stx => pure stx
    | .error e => throwError s!"parse error in synthesised \
        defFn:\n---\n{src}\n---\n{e}"
  let userIdents := collectUserIdents fieldNeedle stx
  let some userStx := userIdents[0]?
    | throwError s!"checkFieldProjGotoDef: expected '{fieldNeedle}' \
        in parsed src, found {userIdents.size} occurrences"
  let some userPos := userStx.getPos?
    | throwError s!"checkFieldProjGotoDef: '{fieldNeedle}' \
        has no source position"
  let positivePred : Lean.Elab.Info → Bool := fun info =>
    match info with
    | .ofTermInfo ti =>
      exprMentions positiveTarget ti.expr
        && (match ti.stx.getPos? with
            | some p => p.byteIdx == userPos.byteIdx
            | none => false)
    | _ => false
  let negativePred : Lean.Elab.Info → Bool := fun info =>
    match info with
    | .ofTermInfo ti => exprMentions negativeTarget ti.expr
    | _ => false
  let foundPositiveRef ← IO.mkRef false
  let foundNegativeRef ← IO.mkRef false
  withInfoTreeContext (mkInfoTree := fun trees => do
      if trees.any (fun t =>
          (t.findInfo? positivePred).isSome) then
        foundPositiveRef.set true
      if trees.any (fun t =>
          (t.findInfo? negativePred).isSome) then
        foundNegativeRef.set true
      return InfoTree.node
        (Info.ofCommandInfo
          { elaborator := `checkFieldProjGotoDef, stx })
        trees) do
    elabCommand stx
  let foundPositive ← foundPositiveRef.get
  let foundNegative ← foundNegativeRef.get
  unless foundPositive do
    throwError s!"field-proj gotoDef regression: no TermInfo \
      mentions {positiveTarget} at the user-source byte offset \
      ({userPos.byteIdx}) of '{fieldNeedle}' in:\n\
      ---\n{src}\n---\n\
      The `(recv).field` parenthesisation + struct-field \
      graft must splice the user-source field token over the \
      parsed-from-string copy so Lean's `Term.proj` elaborator \
      records a type-correct TermInfo at the user position."
  if foundNegative then
    throwError s!"field-proj gotoDef regression: a TermInfo \
      mentions {negativeTarget} in the elaboration of:\n\
      ---\n{src}\n---\n\
      The over-emission from per-candidate `recordIdentRef` \
      should be gone — `recordStructFieldRef` defers field \
      resolution to Lean's `Term.proj` elaborator, which uses \
      the receiver's type and so picks only \
      {positiveTarget}."

elab "checkFieldProjGotoDef" : command => do
  -- `prov ↦ id` against `(prov : Provenance)`. `id` is a
  -- field on both `Provenance` and `RegionVid`, but only
  -- `Provenance.id` is type-correct here. After the buffer
  -- change + `(recv).field` parenthesisation, the
  -- elaborator's TermInfos pin `Provenance.id` to the
  -- user-source `id` token's byte offset, and the bogus
  -- `RegionVid.id` leaf is gone.
  checkFieldProjGotoDef
    "defFn testFieldDecl (.plain \"testFieldDecl\") \
       (.plain \"Field test.\") \
       (prov \"Test param.\" : Provenance) \
       : AllocId := prov ↦ id"
    `Provenance.id `RegionVid.id `id
  -- Chained case: `prov ↦ id ↦ index`. Both `id` and `index`
  -- are ambiguous field names — `index` is also a field on
  -- `Local`, `Body` (basic block index), `EarlyBoundRegion`,
  -- and `LifetimeProjection`. The receiver chain forces the
  -- type-correct picks `Provenance.id` then `AllocId.index`;
  -- the bogus per-candidate leaves for `Local.index` etc.
  -- must be gone for the chained projection too. `index`
  -- appears once in the source so the position pin is
  -- unambiguous.
  checkFieldProjGotoDef
    "defFn testFieldChainDecl (.plain \"testFieldChainDecl\") \
       (.plain \"Chained field test.\") \
       (prov \"Test param.\" : Provenance) \
       : Nat := prov ↦ id ↦ index"
    `AllocId.index `Local.index `index

namespace Wrap
checkFieldProjGotoDef
end Wrap

-- Method-call gotoDef relies on `resolveFnByShortName`:
-- given a method name like `"bodyPlaces"`, it consults the
-- `defFn` registry merged with the current environment's
-- `<X>.<name>.fnDef` constants and returns the qualified
-- Lean name(s) of every defFn that exposes that short
-- name, so the parser can attach a `TermInfo` leaf at the
-- user's `body·bodyPlaces` token.
run_cmd do
  let env ← Lean.MonadEnv.getEnv
  let resolved ← resolveFnByShortName env "bodyPlaces"
  let expected : Lean.Name := `Body ++ `bodyPlaces
  unless resolved.contains expected do
    throwError s!"resolveFnByShortName on `bodyPlaces` \
      returned {resolved}; expected to include {expected}"

-- ══════════════════════════════════════════════
-- Build-time check: gotoDef from a usage of an
-- argument or `let`-bound variable
-- ══════════════════════════════════════════════
--
-- Each `defFn`/`defProperty` body that references a
-- parameter or `let`-bound variable must, after the in-tree
-- DSL elaboration of the synthesized `def`, carry a
-- `TermInfo` whose source range falls on the *user-source*
-- usage occurrence. Without this, LSP gotoDef on a local var
-- in the DSL source dead-ends at synthetic positions inside
-- the rendered string.
--
-- The pipeline that gives us this is:
--   1. `parsePat` and the param-parsing loop record each
--      binder ident syntax into `localBinderBuffer`.
--   2. `parseExpr` records each variable usage into
--      `identRefBuffer` (existing flow, also used for
--      global-ref `addConstInfo`).
--   3. `graftLocalIdentsFromBuffers` builds a per-name FIFO
--      queue from both buffers and, for each ident node in
--      the parsed-from-string defStr, replaces it with the
--      next user-source syntax for that name.
--   4. The elaborator processes the grafted syntax and emits
--      `TermInfo` leaves at the user-source usage positions.
--
-- The tests below elaborate synthetic defFn / defProperty
-- bodies and verify that after elaboration a `TermInfo` for
-- the parameter usage / `let`-bound usage lands at the user-
-- source byte offset (i.e. the *second* occurrence of the
-- name in the parsed src — the first is the binder).
open Lean Elab Command in
/-- Run `defFn`-style command `src` and check that after
    elaboration there's a `TermInfo` whose `stx` is the
    `nameNeedle` identifier at the *user-source* position of
    its `occurrenceIdx`-th occurrence in the parsed src.
    `occurrenceIdx = 1` typically targets the first usage of
    a binder (occurrence 0 is the binder itself). -/
private def checkLocalIdentInfoAt
    (src : String) (nameNeedle : Name)
    (occurrenceIdx : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `command src with
    | .ok stx => pure stx
    | .error e => throwError s!"parse error in synthesised \
        defFn:\n---\n{src}\n---\n{e}"
  let userIdents := collectUserIdents nameNeedle stx
  let some userStx := userIdents[occurrenceIdx]?
    | throwError s!"checkLocalIdentInfoAt: expected at least \
        {occurrenceIdx + 1} occurrences of '{nameNeedle}' in \
        parsed src, found {userIdents.size}"
  let some userPos := userStx.getPos?
    | throwError s!"checkLocalIdentInfoAt: occurrence \
        {occurrenceIdx} of '{nameNeedle}' has no source position"
  let foundRef ← IO.mkRef false
  let pred : Lean.Elab.Info → Bool := fun info =>
    match info with
    | .ofTermInfo ti =>
      ti.stx.getKind == Lean.identKind &&
      ti.stx.getId == nameNeedle &&
      (match ti.stx.getPos? with
        | some p => p.byteIdx == userPos.byteIdx
        | none => false)
    | _ => false
  withInfoTreeContext (mkInfoTree := fun trees => do
      if trees.any (fun t => (t.findInfo? pred).isSome) then
        foundRef.set true
      return InfoTree.node
        (Info.ofCommandInfo
          { elaborator := `checkLocalIdentInfoAt, stx })
        trees) do
    elabCommand stx
  let found ← foundRef.get
  if !found then
    throwError s!"local-ident gotoDef regression: no TermInfo \
      lands on occurrence {occurrenceIdx} of '{nameNeedle}' \
      (byte offset {userPos.byteIdx}) in:\n---\n{src}\n---\n\
      The graftLocalIdentsFromBuffers pass is not preserving \
      user-source positions for local idents, so LSP gotoDef \
      on a parameter or let-bound usage would dead-end at the \
      cursor."

elab "checkLocalIdentInfoAt" : command => do
  -- Parameter usage: `n` appears as binder in `(n : Nat)` and
  -- again as a usage in the body `n + 1`. The graft must
  -- splice the user-source `n` over the rendered defStr's
  -- second `n` ident so a TermInfo lands on the usage.
  checkLocalIdentInfoAt
    "defFn testParamUsage (.plain \"testParamUsage\") \
       (.plain \"Tests gotoDef on a parameter usage.\") \
       (n \"Test param.\" : Nat) \
       : Nat := n + 1"
    `n 1
  -- Let-bound usage: `let x := 1; x + 1`. `x` appears as
  -- binder, then as a usage in `x + 1`. The pat-parser
  -- records the binder; the body's `x` is a usage; the graft
  -- pairs them in source order.
  checkLocalIdentInfoAt
    "defFn testLetUsage (.plain \"testLetUsage\") \
       (.plain \"Tests gotoDef on a let-bound usage.\") \
       : Nat := \
         let x := 1 ; \
         x + 1"
    `x 1
  -- Two parameter usages: `n + n`. The graft must pair the
  -- binder with the binder, and each usage with each usage in
  -- source order. Verify the *second* usage (occurrence 2).
  checkLocalIdentInfoAt
    "defFn testTwoParamUsages (.plain \"testTwoParamUsages\") \
       (.plain \"Tests gotoDef on two parameter usages.\") \
       (n \"Test param.\" : Nat) \
       : Nat := n + n"
    `n 2
  -- defProperty body referencing a parameter usage. Same
  -- pipeline through DefProperty's elabPropertyDecl.
  checkLocalIdentInfoAt
    "defProperty testPropParamUsage \
       (.plain \"testPropParamUsage\") \
       short (.seq [.plain \"short\"]) \
       long (.seq [.plain \"long\"]) \
       (n \"Test param.\" : Nat) \
       := n < 10"
    `n 1

namespace Wrap
checkLocalIdentInfoAt
end Wrap

end Tests.DslGotoDef
