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
├── Runtime/               -- Shared Lean runtime helpers (see below)
├── RuntimeRust/           -- Shared Rust runtime helpers (see below)
├── MIR/                   -- MIR-level definitions
├── OpSem/                 -- Operational semantics
├── PCG/                   -- Place Capability Graph
├── scripts/runLinter.lean              -- Custom lint driver
├── scripts/CheckBannedPatterns.lean    -- Banned-pattern AST audit
├── scripts/CheckUnusedExports.lean     -- Unused-export CI check
├── scripts/unused_exports_allowlist.json -- Exemptions for the above
├── Core.lean              -- Root import for Core lib
├── Runtime.lean           -- Root import for Runtime lib
├── MIR.lean               -- Root import for MIR lib
├── OpSem.lean             -- Root import for OpSem lib
├── PCG.lean               -- Root import for PCG lib
├── Properties.lean        -- Bridge between PCG and OpSem
├── Properties/            --   submodules: Definitions, Aliasing, Soundness
├── Presentation.lean      -- LaTeX presentation builder (depends on PCG)
├── LeanExport.lean        -- `lake exe lean_export`
├── RustExport.lean        -- `lake exe rust_export`
├── PresentationExport.lean -- `lake exe presentation_export`
├── ExportAll.lean         -- Runs all three exporters
├── Tests.lean             -- LSpec test suite
└── lakefile.lean          -- Lake package definition
```

The "content" libraries (`MIR`, `OpSem`, `PCG`) build on top of
`Core` (the DSL) and `Runtime` (small helpers used by DSL-generated
code). `OpSem` and `PCG` are deliberately independent — neither
imports the other. The `Properties` library is the only place the
two libraries are combined; it is split into three submodules:

* `Properties.Definitions` — supporting helpers (`Reachable`,
  `describes`, `analyzeProgram`, `pcgAnalysisSucceeds`,
  `entryStateAt`, `Machine.placeAllocation`, `hasCapability`,
  `hasAllocation`).
* `Properties.Aliasing` — `Framing` and `NoAlias`.
* `Properties.Soundness` — the top-level `Soundness` statement.

Everything else is tooling.

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
   `Lean.Name` of the module it was declared in. This means
   every `defFn` automatically produces a Lean definition, a
   Rust function, and a LaTeX rendering — there is no need to
   duplicate the implementation in exporter-specific extras.

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

## The `RuntimeRust/` library

`RuntimeRust/` is the Rust counterpart to `Runtime/`: a small,
hand-written Cargo crate (`formal-runtime`) that owns the
shared helpers the Rust-export DSL emits calls to. Today it
contains:

- `RuntimeRust/src/map.rs` — `HashMap`-based helpers
  (`map_empty`, `map_singleton`, `map_insert`, `map_remove`,
  `map_at`, `map_get`, `map_values`, `map_union_sets`)
  paralleling `Runtime/Map.lean`.
- `RuntimeRust/src/set.rs` — `HashSet`-based helpers
  (`set_singleton`, …) paralleling `Runtime/Set.lean`.
- `RuntimeRust/src/list.rs` — slice / `Vec` helpers
  (`last`, `replicate`, `list_set`, `list_take`, `list_drop`).

The crate uses `#![deny(clippy::all)]` and
`#![deny(clippy::pedantic)]` so the helpers are held to the
same lint bar as the rest of the project.

**The entire `RuntimeRust/` folder is copied verbatim into
the generated Rust workspace** by `RustExport.main`, landing
at `generated/rust/formal-runtime/`. Each generated crate
(`formal-mir`, `formal-opsem`, `formal-pcg`) carries a path
dependency on `formal-runtime` (`runtimeDep` in
`RustExport.lean`). Modules that need the helpers expose
them with a one-line item such as
`pub use formal_runtime::map::*;` (declared in the relevant
`ExtraSpec.items` entry), so DSL-emitted calls like
`map_get(...)`, `last(...)` resolve through a single source
of truth.

This setup means:

- The in-tree formalization and the exported workspace share
  one copy of every helper — no duplicate string-literal
  helper bodies in `RustExport.lean`.
- Adding a new Rust helper is a matter of dropping a function
  into `RuntimeRust/src/{map,set,list}.rs` (or a new module)
  and re-exporting it from the consumer module via an
  `ExtraSpec.items` entry containing
  `.raw "pub use formal_runtime::<module>::*;"`.

There is one dependency-direction constraint: `formal-runtime`
sits at the bottom of the workspace, so helpers that
reference downstream types (e.g. `AbstractByte`, `IntValue`
from `formal-opsem`) cannot live in `RuntimeRust/`. Such
helpers stay inline in their consumer's `ExtraSpec.items`
`.raw` block — for example, `encode_le_unsigned` and
`int_value_of_nat` remain inline in the `OpSem` decode
module.

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
  `generated/rust/`, ready for `cargo check`. Per-module
  Rust extras (hand-rolled `use` directives, trait impls,
  `pub use formal_runtime::…` re-exports) are declared as
  entries of `extras : List ExtraSpec` and folded into the
  matching module's `extraUses` / `extraItems`.
  `RustExport.main` also copies `RuntimeRust/` verbatim into
  `generated/rust/formal-runtime/` and adds the path
  dependency on it to every generated crate.
- `PresentationExport.lean` → `Presentation.lean` — builds
  one `\section` per crate and one `\subsection` per
  second-level module. Modules nested any deeper
  (e.g. `OpSem.Expressions.Place`) are rendered as
  `\subsubsection`s inside their depth-2 ancestor, with titles
  of the form `"{last component} {parent last component}"` (so
  `OpSem.Expressions.Place` → `"Place Expressions"`).
  The same exporter also walks `Registry.presentations` and
  writes one `<filename>.pdf` per registered template
  presentation (see *Template presentations* below).

## Template presentations

Alongside the monolithic full PDF, users can declare focused
"template" presentations that contain only chosen registered
definitions. The user-facing data type is

```lean
inductive PresElement where
  | doc (d : Doc)
  | defRef (name : String)

structure Presentation where
  elems    : List PresElement
  filename : String
  title    : String := ""
```

A `Presentation` value is registered with the global
presentation registry via `registerPresentation` (a small
wrapper command in `Core/Dsl/RegisterPresentation.lean` that
threads the source module's `Lean.Name` through to
`registerPresentationDef`). At export time
`Presentation/Template.lean :: buildTemplatePresentationLatex`:

1. Resolves each `defRef` name against `Registry.lookupKind`
   (struct / enum / alias / fn / property /
   inductiveProperty / theorem); unknown names abort the
   export with a hard error.
2. Walks the dependency graph (reusing the `referencedNames`
   / `referencedTypes` helpers from `Core/Export/Lean.lean`)
   to compute the transitive closure of every reachable
   registered definition.
3. Splits the closure into the explicitly-listed names
   (rendered in the body, in `elems` order) and the
   appendix names (rendered under an `\section*{Appendix}`
   block, ordered by kind to mirror `renderRegistryItems`).
4. Builds a sub-`Registry` containing only the closure and a
   `RenderCtx` over that sub-registry, so cross-reference
   anchors point only inside the template — making each
   template PDF fully self-contained.

`Presentation/Templates/Example.lean` ships a minimal
`placeTemplate` that embeds `Place` and exercises the
appendix logic across `Local`, `ProjElem`, `FieldIdx`,
`Ty`, `VariantIdx`, and their further transitive
dependencies. CI's existing `lake exe presentation_export`
step builds this template on every push.

### Feature flags

A `Presentation` may opt out of selected DSL features for its
own PDF via the `disabledFeatures : List Feature` field
(empty by default → every feature enabled).

```lean
inductive Feature where
  | enumTypes
  -- new constructors land here
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited, Lean.Quote
```

Each `defEnum` variant and `defFn` / `defProperty` /
inline-`match` arm may carry a `[feature ID, …]` prefix
naming one or more features it is gated on. The LaTeX
exporter drops the variant or arm whenever any of its
features appears in the active presentation's
`disabledFeatures`. The Lean and Rust exports ignore the
`features` field entirely — generated code stays exhaustive.

Arm gating is **derived**: the LaTeX filter unions an arm's
explicit `features` with the features inherited from any
variant referenced by the arm's patterns (recursive over
nested `BodyPat.ctor`s — see `BodyPat.inheritedFeatures`).
So tagging a variant once auto-elides every arm whose
pattern matches it; the explicit `[feature …]` arm prefix
is only needed when an arm is gated on a feature *beyond*
those of the variants it references.

```lean
defEnum ProjElem (.raw "π", .raw "Π")
  "Projection Elements"
  (doc! "…")
where
  | deref "Dereference."
    (MathDoc.doc (.code "*"))
  | [feature ENUM_TYPES] downcast (variant : VariantIdx)
    "Downcast an enum to a specific variant."
    (mathdoc! "@{variant}")
  …

defFn expansionOfStep …
  : PlaceExpansion InitTree where
  | .deref ; child => .deref child
  -- The `[feature ENUM_TYPES]` prefix below is now redundant:
  -- `.downcast` resolves to a variant tagged ENUM_TYPES, so
  -- the arm is auto-elided when the feature is disabled.
  | .downcast v ; child =>
      .guided (.downcast v child)
  …
```

Feature names in the surface DSL are the upper-snake-case
spelling of the constructor (`ENUM_TYPES → Feature.enumTypes`);
the elaborator (`Core/Dsl/Types/Feature.lean :: identToFeature`)
raises an error at the source position on an unknown spelling.
The constructor and its parser arm both live in
`Core/Dsl/Types/Feature.lean`, so adding a new feature is a
single-file change there (plus documenting the spelling here).

The render-time filter lives at:

* `EnumDef.formalDefLatex` (variants in the `definition`
  block).
* `FnDef.formalDefLatex` (top-level `defFn` / `defProperty`
  arms) and `FnDef.exprLines` (nested-match arms in
  complex RHSs).
* `DslExpr.toDoc`'s `.match_` case (top-level
  inline-match arms inside DSL expressions).

`Presentation.mkRenderCtx` turns the presentation's
`disabledFeatures` into the `RenderCtx.isFeatureDisabled`
predicate that those filters consult.

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

For iterative work on the paper, `python3 scripts/watch_presentation.py`
watches every `.lean` file under `formalization/` and re-runs
`lake exe presentation_export` on each change, so the PDF stays in
sync as you edit. Pass exporter flags after `--`, e.g.
`python3 scripts/watch_presentation.py -- --make-pdf=false`.

If your `defFn` body uses a helper that lives outside the DSL
grammar, the choice of where to add it is determined by which
backend(s) need it:

- **Lean-side runtime helpers** go into `Runtime/` (e.g. a
  new `Runtime/Foo.lean`). They are picked up automatically
  by the in-tree build and copied verbatim into the generated
  Lean project.
- **Rust-side runtime helpers** go into `RuntimeRust/` (a new
  function in `RuntimeRust/src/{map,set,list}.rs`, or a new
  module). To make the helper visible in a generated module,
  add a `pub use formal_runtime::<module>::*;` re-export
  through an `ExtraSpec.items` entry for that module. Helpers
  that reference downstream types (and therefore cannot live
  upstream of their consumer crate) stay as inline `.raw`
  items on the consumer module's `ExtraSpec`.
- **Module-specific typeclass instances or one-off snippets**
  that don't belong in a shared runtime go into
  `extraLeanItems` (in `LeanExport.lean`) or `extras` (in
  `RustExport.lean`), keyed by the consumer module.

## DSL linter (`Core/Dsl/Lint.lean`)

`Core/Dsl/Lint.lean` defines a small linter that runs at
elaboration time over every DSL `match` expression. The first
rule is **`irrefutableMatch`**: a `match` whose every arm has
only irrefutable patterns is just a destructuring binder dressed
up as a match — usually because the scrutinee is a `defStruct`
value and the user reached for `match … with | ⟨a, b⟩ => …
end` instead of the equivalent `let ⟨a, b⟩ := … ; …` form.

`BodyPat.isIrrefutable` decides irrefutability:

- `_` and bare variables match every value.
- `⟨a, b, …⟩` (anonymous-tuple) matches every value iff each
  sub-pattern is itself irrefutable.
- Every other shape (named constructors, list cons / nil,
  numeric literals) can fail and is treated as refutable.

The check is wired into `parseExpr`'s `match` case in
`Core/Dsl/DefFn.lean`, so it fires for any DSL surface that goes
through `parseExpr` — `defFn` bodies (all forms), `defProperty`
bodies, `defInductiveProperty` premises and conclusions, and any
future command that reuses the same parser. When the rule fires,
elaboration aborts with `irrefutableMatch` so the user sees the
problem during `lake build`.

`DslLint.lintExpr` is also exposed as a pure function for unit
tests (see `Tests.lean`) and for any out-of-band lint runner.

## Unused-export CI check (`scripts/CheckUnusedExports.lean`)

`scripts/CheckUnusedExports.lean` is a separate lake exe
(`lake exe check_unused_exports`) that audits `Core` for
non-private declarations no other module references. It is
wired into the `lean` job in `.github/workflows/ci.yml` as the
"Check Core has no unused exports" step, so any new dead
`Core` export fails CI.

The check is structural rather than name-pattern-based: it
imports every user package (`Core`, `MIR`, `OpSem`, `PCG`,
`Properties`, `Presentation`, `Runtime`, `Tests`) into a single
environment, and the four executable roots
(`RustExport`, `LeanExport`, `PresentationExport`,
`ExportAll`) into per-exe environments — each defines its own
`def main`, so they cannot share an environment. Their
referenced-constant sets are merged into a global "is anyone
referencing this" set; every non-private `def` defined in a
`Core.*` module that is missing from the set is reported.

Compiler-generated decls (recursors, match equations,
`derive Repr` / `Inhabited` instances, parser-extension
infrastructure, `_aux_*` elab helpers, French-bracketed syntax
rule names, decls whose declared type's head is
`Lean.ParserDescr` / `Lean.PrettyPrinter.Formatter` /
`Lean.Elab.Term.TermElab` / `Lean.Elab.Command.CommandElab`) are
exempt from the audit.

Exports that legitimately have no compile-time referrer (e.g.
`Core.Dsl.IdentRefs.dslProofMarker`, which is used as a
syntactic placeholder in DSL-rendered Lean source rather than as
a Lean constant) are listed in
`scripts/unused_exports_allowlist.json` together with a
rationale; the check fails loud if a listed name is missing
from the loaded environment, so the file cannot go stale
silently.
