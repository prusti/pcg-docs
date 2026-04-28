import Lean
import Core.Registry

/-!
# DSL LSP support helpers

Buffer + helpers used by `defFn`, `defProperty`, and friends
to make LSP go-to-definition (and hover) work for DSL-level
declarations.

The DSL elaborates each declaration by rendering its body to a
string and re-parsing it via `Parser.runParserCategory`. That
round-trip discards source positions from the original DSL
syntax in two ways:

* Identifier references inside the body lose their user-file
  positions, so gotoDef on `validProgram` in a `defProperty`
  body would land nowhere.
* The synthesised `def`/`inductive` syntax that the elaborator
  sees has positions relative to the rendered string, not the
  user's file. The elaborator records those as the
  declaration's `DeclarationRanges`, so gotoDef *to* the
  declaration lands at the start of the file rather than at the
  user's `defFn`/`defProperty`/... line.

To get both directions of gotoDef back:

* The DSL parser records every potentially global identifier
  (function-call heads, type names in parameters, etc.)
  together with its original `Syntax`. Once the synthesised
  declaration has been elaborated and added the named constant
  to the environment, `flushIdentRefs` resolves each buffered
  name and emits a `TermInfo` leaf at the original `Syntax`'s
  position. The LSP picks those up via the standard info-tree
  machinery.
* After `elabCommand` for the synthesised declaration,
  `setUserDeclRanges` re-registers the declaration's
  `DeclarationRanges` using the original DSL syntax, so gotoDef
  lands on the user's `defFn`/`defProperty` block instead of
  the start of the file.

A single module-level `IO.Ref` is used for the identifier
buffer because `parseExpr`/`parsePat` are partial and mutually
called from many places, which makes threading explicit state
awkward.
-/

namespace Core.Dsl.IdentRefs

/-- Buffer of `(identifierSyntax, name)` pairs collected while
    parsing a DSL body. Each `defFn`/`defProperty`/...
    elab-rule clears the buffer at entry and calls
    `flushIdentRefs` after the generated Lean declaration has
    been elaborated. -/
initialize identRefBuffer :
    IO.Ref (Array (Lean.Syntax × Lean.Name)) ← IO.mkRef #[]

/-- Record an identifier reference for later `TermInfo`
    emission. Called from the parser whenever an `ident` token
    syntactically denotes a potential global reference
    (function call head, free variable, struct/enum
    constructor, higher-order function argument, ...). -/
def recordIdentRef (stx : Lean.Syntax)
    (name : Lean.Name) : IO Unit :=
  identRefBuffer.modify (·.push (stx, name))

/-- Look up a `defStruct` field name in the global struct
    registry and, when exactly one registered struct exposes a
    field of that name, return the qualified Lean constant
    name (e.g. `"functions" → some `Program.functions`).

    Used by the `↦` parser rule to record gotoDef targets for
    field accesses like `program↦functions`: the synthesised
    Lean rendering `program.functions` carries no user-source
    position, so we attach a `TermInfo` leaf at the user's
    `functions` token pointing at `Program.functions` instead.

    Returns `none` if no struct or more than one struct claims
    the name — ambiguous lookups would resolve to the wrong
    declaration, so we conservatively skip them. -/
def resolveStructField (fieldName : String) :
    IO (Option Lean.Name) := do
  let structs ← getRegisteredStructs
  let owners := structs.filterMap fun s =>
    if s.structDef.fields.any (·.name == fieldName) then
      some s.structDef.name
    else none
  match owners with
  | [structName] =>
    pure (some <|
      (Lean.Name.mkSimple structName).append
        (Lean.Name.mkSimple fieldName))
  | _ => pure none

/-- Walk a type-position `Syntax` tree and record every
    identifier inside it via `recordIdentRef`, so the LSP can
    jump from a type name in a parameter or return type
    (e.g. `Body` in `(body : Body)`) to the corresponding
    struct/enum/alias definition. -/
partial def recordTypeIdents
    (stx : Lean.Syntax) : IO Unit := do
  if stx.isIdent then
    recordIdentRef stx stx.getId
  else
    for arg in stx.getArgs do
      recordTypeIdents arg

/-- Take the currently-buffered identifier references and
    empty the buffer, so subsequent invocations start from a
    clean slate. -/
def takeIdentRefs :
    IO (Array (Lean.Syntax × Lean.Name)) := do
  let refs ← identRefBuffer.get
  identRefBuffer.set #[]
  return refs

open Lean Elab Command in
/-- Push a `TermInfo` leaf for each recorded identifier whose
    name resolves to an existing constant, so the LSP can jump
    from a DSL-level identifier to the backing Lean
    definition. Resolution respects the current namespace and
    any `open` declarations in scope, so e.g.
    `writeBytesAt` inside `namespace Memory` correctly
    resolves to `Memory.writeBytesAt`. Identifiers that don't
    resolve (locally bound variables, forward references
    inside a mutual group that hasn't been elaborated yet,
    ...) are silently skipped. -/
def flushIdentRefs : CommandElabM Unit := do
  let refs ← takeIdentRefs
  let env ← getEnv
  let ns ← getCurrNamespace
  let opens ← getOpenDecls
  let opts ← getOptions
  for (stx, name) in refs do
    let candidates :=
      Lean.ResolveName.resolveGlobalName env opts ns opens name
    let resolved := candidates.filterMap fun (n, parts) =>
      if parts.isEmpty && env.contains n then some n else none
    match resolved with
    | [n] => addConstInfo stx n
    | _ => pure ()

open Lean Elab Command in
/-- After elaborating a DSL-synthesised declaration, override
    its recorded `DeclarationRanges` so gotoDef *to* the
    declaration lands on the original `defFn`/`defProperty`/...
    block in the user's source file rather than at the start of
    the file (which is where the synthetic syntax parsed from
    the rendered string ends up).

    `name` is the unqualified declaration identifier as written
    in the DSL; the current namespace is prepended to obtain
    the fully-qualified constant name registered by
    `elabCommand`. `rangeStx` is the entire user `defFn`/...
    block (typically `← getRef`); `name.raw` doubles as the
    selection range so the LSP highlights just the identifier
    when it lands on the definition. -/
def setUserDeclRanges (name : Ident)
    (rangeStx : Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ name.getId
  Lean.Elab.addDeclarationRangesFromSyntax declName rangeStx
    name.raw

end Core.Dsl.IdentRefs
