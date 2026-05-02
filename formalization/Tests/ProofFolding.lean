import Core.Dsl.DefFn
import Lean

/-!
# Build-time checks: `proof[…]` folding is reachable from any DSL file

`Core.Dsl.ProofFolding` registers a chained `textDocument/foldingRange`
handler in its `initialize` block. The handler is only effective in
file-worker environments where the module has been loaded — i.e.,
where some module in the file's import graph imports
`Core.Dsl.ProofFolding`.

DSL-using files (`OpSem/*`, `PCG/*`, …) typically import
`Core.Dsl.DefFn` directly rather than going through the umbrella
`Core` module. So `Core.Dsl.DefFn` must transitively import
`Core.Dsl.ProofFolding` for the LSP folding chain to be active when
those files are open in the editor.

This file imports *only* `Core.Dsl.DefFn` and then references
identifiers from `Core.Dsl.ProofFolding`. If the transitive import is
ever removed, this file will fail to compile, surfacing the
regression at build time. -/

namespace Tests.ProofFolding

open Lean Lean.Server Core.Dsl.ProofFolding

-- Compile-time witness that `Core.Dsl.DefFn` transitively imports
-- `Core.Dsl.ProofFolding` (and therefore loads it into any LSP
-- file-worker that imports `defFn`).
example : Lean.Syntax → Bool := isProofBracket
example : FileMap → Lean.Syntax → Array Lsp.FoldingRange
    → Array Lsp.FoldingRange := collectProofRanges

private def multilineSrc : String :=
"defFn testFoldFn (.plain \"testFoldFn\")
    (.plain \"Test fn.\")
    : Nat := proof[Nat.add
                    1
                    2]
"

private def singleLineSrc : String :=
"defFn testFoldFn (.plain \"testFoldFn\")
    (.plain \"Test fn.\")
    : Nat := proof[1]
"

run_cmd do
  let env ← getEnv
  let stx ← match Lean.Parser.runParserCategory env `command
      multilineSrc with
    | .ok stx => pure stx
    | .error e => throwError
        s!"multi-line parse failed: {e}\n---\n{multilineSrc}\n---"
  let text : FileMap := FileMap.ofString multilineSrc
  let ranges := collectProofRanges text stx #[]
  unless ranges.size ≥ 1 do
    throwError s!"expected ≥1 fold range for multi-line `proof[…]`, \
      got {ranges.size}"
  let isRegion (k : Option Lsp.FoldingRangeKind) : Bool :=
    match k with | some .region => true | _ => false
  let onProofRange := ranges.any fun r =>
    isRegion r.kind? && r.startLine + 1 ≤ r.endLine
  unless onProofRange do
    throwError s!"expected a multi-line `region` fold range, got \
      {ranges.size} ranges"

run_cmd do
  let env ← getEnv
  let stx ← match Lean.Parser.runParserCategory env `command
      singleLineSrc with
    | .ok stx => pure stx
    | .error e => throwError
        s!"single-line parse failed: {e}\n---\n{singleLineSrc}\n---"
  let text : FileMap := FileMap.ofString singleLineSrc
  let ranges := collectProofRanges text stx #[]
  -- A single-line `proof[…]` must NOT produce a fold range, since
  -- LSP folding ranges have to span multiple lines.
  let isRegion (k : Option Lsp.FoldingRangeKind) : Bool :=
    match k with | some .region => true | _ => false
  let proofLine := 3 -- `: Nat := proof[1]` line in `singleLineSrc`
  let bogus := ranges.any fun r =>
    isRegion r.kind? && r.startLine == proofLine
        && r.endLine == proofLine
  if bogus then
    throwError s!"single-line `proof[…]` should not fold, got \
      {ranges.size} ranges"

end Tests.ProofFolding
