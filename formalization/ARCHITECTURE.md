# Formalization architecture

This directory contains a Lean 4 formalization of the Place
Capability Graph (PCG) for MIR. Most of the formalization is
written in a custom DSL (`defStruct`, `defEnum`, `defFn`,
`defProperty`, `defOrder`) whose sources are consumed by three
backend exporters — LaTeX (for the paper), Rust (for the
runtime crate), and Lean itself (for a standalone, cleaned-up
copy of the definitions).

## Top-level layout

```
formalization/
├── Core/                  -- DSL definitions + backends
├── Runtime/               -- Shared runtime helpers (see below)
├── MIR/                   -- MIR-level definitions
├── OpSem/                 -- Operational semantics
├── PCG/                   -- Place Capability Graph
├── scripts/runLinter.lean -- Custom lint driver
├── Core.lean              -- Root import for Core lib
├── Runtime.lean           -- Root import for Runtime lib
├── MIR.lean               -- Root import for MIR lib
├── OpSem.lean             -- Root import for OpSem lib
├── PCG.lean               -- Root import for PCG lib
├── LeanExport.lean        -- `lake exe lean_export`
├── RustExport.lean        -- `lake exe rust_export`
├── PresentationExport.lean -- `lake exe presentation_export`
├── ExportAll.lean         -- Runs all three exporters
├── Tests.lean             -- LSpec test suite
└── lakefile.lean          -- Lake package definition
```

The four "content" libraries (`MIR`, `OpSem`, `PCG`) build on
top of `Core` (the DSL) and `Runtime` (small helpers used by
DSL-generated code). Everything else is tooling.

## The DSL (`Core/Dsl/`)

The `defStruct`, `defEnum`, `defFn`, `defProperty`, and
`defOrder` commands in `Core/Dsl/` elaborate to two things in
parallel:

1. **Real Lean definitions.** `defFn evalLocal (...) : ...
   begin ... end` elaborates to a plain Lean `def
   Machine.evalLocal ... := ...` that participates in Lean's
   type-checking exactly like any other definition.
2. **Registry entries.** Each DSL command also calls a
   `registerXDef` so the backend exporters can later enumerate
   every `defStruct` / `defEnum` / `defFn` / ... along with the
   `Lean.Name` of the module it was declared in.

DSL function bodies are parsed into a `DslExpr` AST (see
`Core/Dsl/Types/DslExpr.lean`). `DslExpr` is the
backend-agnostic IR that each exporter lowers into its own
target syntax:

- `Core/Export/Lean.lean` → `LeanExpr` → generated Lean source
- `Core/Export/Rust.lean` → `RustExpr` → generated Rust source
- `Core/Dsl/Types/DslExpr.lean :: toDoc` → `MathDoc` →
  `LatexMath` → presentation PDF

Because function bodies go through a single AST, a change in
one DSL body propagates to all three backends automatically.

## The `Runtime/` library

`Runtime/` is a small, hand-written Lean library that provides
primitive types and helpers the DSL relies on. Today it
contains:

- `Runtime/Set.lean` — the `Set α` abbreviation over
  `Std.HashSet`, plus a handful of helpers (`Set.singleton`,
  `Set.union`, `Set.flatMapList`, `Option.toSet`, …).
- `Runtime/Map.lean` — the `Map κ ν` abbreviation over
  `Std.HashMap`, plus `mapGet`.

Anything DSL-generated code calls out to that is not itself a
`defFn` goes here. For example, `defFn evalLocal`'s body uses
`mapGet ‹machine↦locals, lcl›`; the DSL parses `mapGet` as a
free function call and the Lean backend lowers it to `mapGet
machine.locals lcl`, which is resolved against
`Runtime.Map.mapGet`.

**The entire `Runtime/` folder is copied verbatim into the
generated Lean project** by `LeanExport.lean`. This means:

- The in-tree formalization and the exported project share a
  single source of truth for these helpers.
- Adding a new helper is a matter of dropping a file under
  `Runtime/` (and teaching `computeImports` to pull in that
  module when appropriate). There is no separate string-literal
  copy of the code in `LeanExport.lean` to keep in sync.

Because `defFn` bodies are elaborated in the formalization
build, any file that uses the DSL must have `Runtime` in its
import graph. This is handled for you: `Core/Dsl/DefFn.lean`
does `import Runtime`, so any file importing the DSL gets
`Set`, `Map`, and `mapGet` transitively in scope.

For the generated project, `LeanExport.computeImports` adds
explicit `import Runtime.Set` / `import Runtime.Map` to each
generated module based on which of those helpers the module's
contents actually reference.

## Registries and exporters

Each DSL command appends to a global `IO.Ref` registry (see
`Core/Registry.lean`). At export time, the exporter reads the
registries and groups entries by their `leanModule` (the module
in which they were declared):

- `LeanExport.lean` — writes each group out as a standalone
  Lean file under `generated/lean/`, then runs `lake build` on
  the result. Also copies `Runtime/` as described above.
- `RustExport.lean` — lowers each group to a `RustCrate`
  (`formal-mir`, `formal-opsem`, `formal-pcg`) under
  `generated/rust/`, ready for `cargo check`.
- `PresentationExport.lean` → `PCG/Presentation.lean` — builds
  one `\section` per crate and one `\subsection` per
  second-level module. Modules nested any deeper
  (e.g. `OpSem.Expressions.Place`) are rendered as
  `\subsubsection`s inside their depth-2 ancestor, with titles
  of the form `"{last component} {parent last component}"` (so
  `OpSem.Expressions.Place` → `"Place Expressions"`).

## Adding a new definition

The common case is adding or moving a `defFn`. For example, to
add a new function to `OpSem/Expressions/Place.lean`:

1. Write the `defFn` in that file using the DSL syntax.
2. `lake build` — elaborates the DSL, registers the function,
   and type-checks the generated Lean definition.
3. `lake exe lean_export` — regenerates
   `generated/lean/OpSem/Expressions/Place.lean` (and rebuilds
   the generated project).
4. `lake exe rust_export` — regenerates
   `generated/rust/formal-opsem/src/place.rs`.
5. `lake exe presentation_export` — regenerates the PDF.

`lake exe export_all` runs all three.

If your `defFn` body uses a helper that lives outside the DSL
grammar, add it to `Runtime/` (for runtime-style helpers) or
to `extraLeanItems` / `extraItems` (for module-specific
typeclass instances or one-off Rust snippets) in
`LeanExport.lean` / `RustExport.lean`.
