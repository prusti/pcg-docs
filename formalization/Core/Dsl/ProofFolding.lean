import Lean
import Lean.Server
import Lean.Server.Requests
import Lean.Server.Snapshots

/-! # Folding ranges for `proof[…]` blocks

DSL `proof[…]` blocks frequently expand across many lines
(rewrite chains, `match h : …` scrutinees, intermediate `have`
clauses), but Lean's stock LSP folding-range handler only emits
ranges at the command level — the whole `defFn`/`defProperty`
collapses to a single line, with no way to fold the proof body
in isolation.

This module chains an additional folding-range provider onto the
default one. After the standard handler returns its
command-level ranges, we walk every parsed command snapshot,
descend into its syntax tree, and emit a `region`-kind folding
range for each `proof[…]` node that spans more than one line.
The result is the union of Lean's built-in ranges and the new
ones, so the existing per-command folding is preserved
unchanged. -/

namespace Core.Dsl.ProofFolding

open Lean Lean.Lsp Lean.Server Lean.Server.FileWorker
open Lean.Server.RequestM
open Lean.Server.Snapshots (Snapshot)

/-! ## `FromJson` instances

`chainLspRequestHandler` requires a `FromJson` instance on the
response type so the previous handler's output can be re-parsed
before being passed to the chained handler. Lean's stock
`FoldingRange`/`FoldingRangeKind` types only derive `ToJson`,
so we add the inverse direction here. The serialisation choices
(string tags `"comment"`/`"imports"`/`"region"` and the
`startLine`/`endLine`/`kind?` field names) match the LSP spec
and Lean's `ToJson` encoder. -/

instance : FromJson FoldingRangeKind where
  fromJson?
    | .str "comment" => .ok .comment
    | .str "imports" => .ok .imports
    | .str "region"  => .ok .region
    | _ => .error
        "expected one of \"comment\", \"imports\", \"region\""

instance : FromJson FoldingRange where
  fromJson? j := do
    let startLine ← j.getObjValAs? Nat "startLine"
    let endLine ← j.getObjValAs? Nat "endLine"
    -- Lean's `ToJson` derive strips the trailing `?` from the
    -- Lean field name `kind?` when serialising, so the JSON key
    -- is `"kind"`. Try both forms — `kind` first — and fall
    -- back to `none` if neither is present.
    let kindRaw? := j.getObjVal? "kind" |>.toOption
      |>.orElse fun _ => j.getObjVal? "kind?" |>.toOption
    let kind? ← match kindRaw? with
      | none   => .ok none
      | some v => some <$> fromJson? v
    return { startLine, endLine, kind? }

/-! ## Syntax-tree walk -/

/-- Whether `stx` is the parsed form of a `proof[term]`
    expression. The DSL declares this via
    `syntax:max "proof[" term "]" : fnExpr`, so the parsed node's
    first child is the literal atom `"proof["`; we don't need to
    care about the auto-generated kind name. -/
def isProofBracket (stx : Syntax) : Bool :=
  match stx with
  | .node _ _ args =>
    if h : args.size > 0 then
      match args[0] with
      | .atom _ "proof[" => true
      | _ => false
    else false
  | _ => false

/-- Push a `region` folding range covering `stx`'s extent onto
    `acc`, when `stx` has a known source position and spans more
    than one line. Single-line `proof[…]` calls don't need to
    fold (and VS Code rejects single-line ranges anyway). -/
private def pushRangeIfMultiline
    (text : FileMap) (stx : Syntax) (acc : Array FoldingRange)
    : Array FoldingRange :=
  match stx.getPos?, stx.getTailPos? with
  | some startP, some endP =>
    let s := text.utf8PosToLspPos startP
    let e := text.utf8PosToLspPos endP
    if s.line < e.line then
      acc.push
        { startLine := s.line
          endLine   := e.line
          kind?     := some .region }
    else acc
  | _, _ => acc

/-- Walk a syntax tree, appending a folding range for every
    `proof[…]` node that spans multiple lines. -/
partial def collectProofRanges
    (text : FileMap) (stx : Syntax) (acc : Array FoldingRange)
    : Array FoldingRange :=
  let acc :=
    if isProofBracket stx then pushRangeIfMultiline text stx acc
    else acc
  match stx with
  | .node _ _ args =>
    args.foldl
      (fun acc child => collectProofRanges text child acc) acc
  | _ => acc

/-! ## Chained LSP handler -/

private def chainedHandler
    (_ : FoldingRangeParams)
    (existingTask : RequestTask (Array FoldingRange))
    : RequestM (RequestTask (Array FoldingRange)) := do
  let doc : EditableDocument ← readDoc
  let text : FileMap := doc.meta.text
  let snapsTask := doc.cmdSnaps.waitAll
  RequestM.bindRequestTaskCheap existingTask fun existing =>
    RequestM.mapTaskCheap snapsTask fun
        (snaps : List Snapshot × Option IO.Error) => do
      let mut acc := existing
      for snap in snaps.fst do
        acc := collectProofRanges text snap.stx acc
      return acc

initialize
  chainLspRequestHandler "textDocument/foldingRange"
    FoldingRangeParams (Array FoldingRange) chainedHandler

end Core.Dsl.ProofFolding
