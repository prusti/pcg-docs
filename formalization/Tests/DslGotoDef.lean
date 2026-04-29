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
  short (xDoc) =>
    (.seq [.plain "test about ", xDoc])
  long (xDoc) =>
    (.seq [.plain "test about ", xDoc])
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
