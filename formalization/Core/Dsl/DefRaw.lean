import Lean

/-!
# `defRaw`: single-source raw-Lean blocks for the Lean export

The DSL can express most of what the export pipeline needs, but
a handful of source files require Lean features the DSL does not
currently model — typeclass `instance` declarations,
`partial def`, `termination_by` / `decreasing_by` clauses, bare
`def name := <expr>` aliases, etc. Historically the affected
declarations lived in two places: as raw Lean in the source file
(so `lake build` accepts them) and as string literals inside
`LeanExport.extraLeanItems` (so the generated Lean project
contains them). The two copies drifted independently.

`defRaw` collapses each pair to a single source of truth. A
source file declares the block once via

```
defRaw beforeProperties =>
  def reachableSearch ... termination_by ... decreasing_by ...
```

and the command

1. elaborates the inner Lean command in the current scope, so
   the source build sees the declaration exactly as written
   AND the IDE keeps full syntax-highlighting / hover /
   go-to-definition support on it;
2. captures the inner command's verbatim source text from
   the file map and records the
   `(currentModule, position, rawText)` triple in a global
   registry that `LeanExport`'s renderer reads at render
   time, replacing the old hard-coded `extraLeanItems`.

Each `defRaw` call carries one top-level Lean command — for
modules that need several declarations in one slot, use
several `defRaw` calls in source order. -/

namespace Core.Dsl

/-- Position of an extra raw-Lean block relative to the
    auto-generated DSL output for a module:

    * `.before` — before the type definitions (top of the
      generated file, after `import` lines).
    * `.middle` — between the type definitions and the
      function definitions.
    * `.beforeProperties` — between the function definitions
      and the `defProperty` definitions; only meaningful for
      modules where every property follows every function.
    * `.after` — after every DSL-generated declaration. -/
inductive ExtraPos where
  | before
  | middle
  | beforeProperties
  | after
  deriving BEq, Repr

/-- A single raw-Lean block targeted at the generated
    `(module, position)` slot. The `code` field is the
    verbatim text — including comments, attributes, typeclass
    instance syntax, and `termination_by` / `decreasing_by`
    clauses — that was elaborated at the `defRaw` call site
    and should be re-emitted into the corresponding generated
    module. -/
structure RawBlock where
  /-- The Lean module that owns the block. -/
  leanModule : Lean.Name
  /-- Where to splice the block in the generated output. -/
  pos : ExtraPos
  /-- Verbatim Lean source. -/
  code : String
  deriving Repr

/-- Module-level registry of raw-Lean blocks declared via
    `defRaw`. Entries are appended in source order; the
    export pipeline reads them once per `(module, position)`
    slot. -/
initialize rawBlockRegistry : IO.Ref (List RawBlock) ←
  IO.mkRef []

/-- Counter used to give each `defRaw` block a unique
    constant name during elaboration. The names don't have
    to be stable across compilations — they only need to be
    unique within a single elaboration run. -/
initialize rawBlockNameCounter : IO.Ref Nat ←
  IO.mkRef 0

/-- Append a `RawBlock` to the registry. Idempotency is not
    enforced — re-running `defRaw` simply re-registers, the
    same way the existing DSL registries behave. -/
def registerRawBlock (b : RawBlock) : IO Unit :=
  rawBlockRegistry.modify (· ++ [b])

/-- Read every registered raw block. Used by `LeanExport` to
    fetch per-module extras at render time. -/
def getRegisteredRawBlocks : IO (List RawBlock) :=
  rawBlockRegistry.get

end Core.Dsl

open Core.Dsl

/-- Parse one of `before` / `middle` / `beforeProperties` /
    `after` from a Lean identifier into the matching
    `ExtraPos` constructor. -/
private def parseExtraPos (id : Lean.Ident) :
    Lean.Elab.Command.CommandElabM ExtraPos := do
  match id.getId with
  | `before => pure .before
  | `middle => pure .middle
  | `beforeProperties => pure .beforeProperties
  | `after => pure .after
  | other =>
    Lean.throwErrorAt id
      s!"defRaw: unknown position '{other}'; expected one of \
        before / middle / beforeProperties / after"

/-- Declare a raw-Lean block scoped to the current module and
    splice it into the matching slot of the generated module.

    The first argument is one of `before`, `middle`,
    `beforeProperties`, `after`; the body is a single Lean
    command, which is elaborated normally (so the IDE keeps
    full highlighting / hover / gotoDef on it) and captured
    verbatim from the file map for the export. Multiple
    declarations in one slot use multiple consecutive
    `defRaw` calls in source order. -/
syntax "defRaw " ident "=>" command : command

/-- Capture the verbatim source text of `stx` from the
    current file map. Used to register the elaborated `defRaw`
    body so the export emits the same characters the user
    typed (including comments and whitespace). Returns the
    empty string if the syntax has no source range — that
    only happens for hand-built `Syntax.missing` nodes, not
    for the parsed body of a `defRaw` command. -/
private def captureSource (stx : Lean.Syntax) :
    Lean.Elab.Command.CommandElabM String := do
  match stx.getRange? with
  | none => pure ""
  | some range =>
    let fm ← Lean.MonadFileMap.getFileMap
    pure (String.Pos.Raw.extract fm.source range.start range.stop)

open Lean Elab Command in
elab_rules : command
  | `(defRaw $pos:ident => $cmd:command) => do
    let posVal ← parseExtraPos pos
    -- Elaborate the inner command in the current scope so
    -- the source build sees the declaration as written.
    elabCommand cmd
    -- Pull the body's verbatim source text out of the file
    -- map. The trailing newline keeps successive blocks
    -- separated when the export concatenates their entries
    -- back into a single per-position chunk.
    let raw := (← captureSource cmd.raw) ++ "\n"
    -- Emit an `initialize` block that re-registers the
    -- raw text every time this module is loaded. The
    -- elab-time `registerRawBlock` invocation only persists
    -- inside the build's `IO.Ref`, so without the
    -- `initialize` the export executable wouldn't see the
    -- block when it imports the compiled `.olean`.
    let mod ← getMainModule
    let modTerm : TSyntax `term := quote mod
    let codeStr : TSyntax `term := quote raw
    let posTerm : TSyntax `term ← match posVal with
      | .before => `(ExtraPos.before)
      | .middle => `(ExtraPos.middle)
      | .beforeProperties =>
        `(ExtraPos.beforeProperties)
      | .after => `(ExtraPos.after)
    -- Generate a unique constant name for this block via
    -- the local counter; multiple `defRaw` calls in one
    -- module bump it independently so the names don't
    -- collide.
    let counter ←
      rawBlockNameCounter.modifyGet fun n => (n, n + 1)
    let blockId : Lean.Ident :=
      mkIdent (Name.mkSimple s!"_rawBlock_{counter}")
    elabCommand (← `(command|
      private def $blockId : RawBlock :=
        { leanModule := $modTerm, pos := $posTerm,
          code := $codeStr }))
    elabCommand (← `(command|
      initialize registerRawBlock $blockId))
