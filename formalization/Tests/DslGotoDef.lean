import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefAlias
import Core.Dsl.DefStruct
import Core.Dsl.IdentRefs
import OpSem.Program
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
  | refl {x : Nat} ⊢ TestInductiveProp ‹x›

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
  -- Direct expression body: `testCaller := testCallee ‹›`.
  checkCallSiteGotoDef
    "defFn testCallerSimple (.plain \"testCallerSimple\") \
       (.plain \"Simple direct caller.\") \
       : Nat := testCallee ‹›"
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
         testCallee ‹›"
    `Tests.DslGotoDef.Wrap.testCallee
  -- Body uses `requires` precondition and a let-chain ending
  -- in the call, fully mirroring `initialMachine`'s shape.
  checkCallSiteGotoDef
    "defFn testCallerReq (.plain \"testCallerReq\") \
       (.plain \"Caller with a precondition + let-chain.\") \
       (n \"Test param.\" : Nat) \
       requires testGuard(n) \
       : Nat := \
         let x := 1 ; \
         testCallee ‹›"
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
       := testGuard ‹n›"
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
            ‹break› testGuard ‹n›"
    `Tests.DslGotoDef.Wrap.testGuard

namespace Wrap
checkCallSiteGotoDef
end Wrap

-- Field-projection gotoDef relies on `resolveStructField`:
-- given a field name like `"functions"`, it consults the
-- `defStruct` registry and returns the qualified Lean name
-- `Program.functions` so the parser can attach a `TermInfo`
-- leaf at the user's `program↦functions` token.
run_cmd do
  let resolved ← resolveStructField "functions"
  match resolved with
  | none =>
    throwError "resolveStructField returned none for \
      `functions`; expected `Program.functions`"
  | some n =>
    let expected : Lean.Name := `Program ++ `functions
    unless n == expected do
      throwError s!"resolveStructField resolved to {n}, \
        expected {expected}"

end Tests.DslGotoDef
