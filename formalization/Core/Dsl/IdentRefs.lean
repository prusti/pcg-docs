import Lean

/-!
# DSL identifier reference tracking

Buffer + helpers used by `defFn`, `defProperty`, and friends
to make LSP go-to-definition (and hover) work for DSL-level
identifiers.

The DSL elaborates each declaration by rendering its body to a
string and re-parsing it via `Parser.runParserCategory`. That
round-trip discards source positions from the original DSL
syntax, so by the time the elaborator sees the rendered Lean
declaration the identifiers no longer carry the user's
file/line info — and `gotoDefinition` from `validProgram` in a
`defProperty` body lands nowhere.

To get gotoDef back, the DSL parser records every potentially
global identifier (function-call heads, type names in
parameters, etc.) together with its original `Syntax`. Once the
synthesised declaration has been elaborated and added the named
constant to the environment, `flushIdentRefs` resolves each
buffered name and emits a `TermInfo` leaf at the original
`Syntax`'s position. The LSP picks those up via the standard
info-tree machinery.

A single module-level `IO.Ref` is used because
`parseExpr`/`parsePat` are partial and mutually called from
many places, which makes threading explicit state awkward.
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

end Core.Dsl.IdentRefs
