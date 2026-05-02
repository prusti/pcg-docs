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

/-- Buffer of original `proof[term]` body syntaxes collected
    while parsing a DSL body, in depth-first / left-to-right
    order. Each `defFn`/`defProperty`/... elab-rule clears the
    buffer at entry; after the generated Lean declaration is
    parsed back from a string, `graftDslProofMarkers` consumes
    the buffer in order to substitute each user-source
    `proof[…]` body in place of the corresponding
    `dslProofMarker (…)` placeholder, restoring the original
    source positions so the InfoView reports the proof goal at
    the user's cursor. -/
initialize proofSyntaxBuffer :
    IO.Ref (Array Lean.Syntax) ← IO.mkRef #[]

/-- Identity function used as a position-grafting placeholder
    for in-tree DSL elaboration of `proof[…]` blocks. Rendered
    around each proof term in the synthesized Lean source; after
    parsing, `graftDslProofMarkers` replaces each marker's
    argument with the user's original `proof[…]` body syntax.
    The marker is `@[inline, reducible]` so it disappears from
    elaborated terms — semantically a no-op identity. -/
@[inline, reducible]
def dslProofMarker {α : Sort _} (x : α) : α := x

/-- Append a parsed `proof[…]` body's syntax to
    `proofSyntaxBuffer`. Called from `parseExpr` whenever a
    `proof[$t:term]` form is encountered. -/
def recordProofSyntax (stx : Lean.Syntax) : IO Unit :=
  proofSyntaxBuffer.modify (·.push stx)

/-- Take the currently-buffered proof-syntax fragments and
    empty the buffer. -/
def takeProofSyntaxes : IO (Array Lean.Syntax) := do
  let buf ← proofSyntaxBuffer.get
  proofSyntaxBuffer.set #[]
  return buf

/-- Record an identifier reference for later `TermInfo`
    emission. Called from the parser whenever an `ident` token
    syntactically denotes a potential global reference
    (function call head, free variable, struct/enum
    constructor, higher-order function argument, ...). -/
def recordIdentRef (stx : Lean.Syntax)
    (name : Lean.Name) : IO Unit :=
  identRefBuffer.modify (·.push (stx, name))

/-- Look up a `defStruct` field name in the global struct
    registry and return the qualified Lean constant name
    (e.g. `"functions" → [`Program.functions]`) for every
    registered struct that exposes that field.

    Used by the `↦` parser rule to record gotoDef targets for
    field accesses like `program↦functions`: the synthesised
    Lean rendering `program.functions` carries no user-source
    position, so we attach a `TermInfo` leaf at the user's
    `functions` token pointing at every matching field
    constant. The LSP merges multiple `TermInfo` leaves at
    the same source position into a single multi-target
    gotoDef list, so a field name claimed by more than one
    struct (e.g. `locals` on both `OwnedState` and
    `StackFrame`) still navigates to candidate definitions
    rather than dead-ending at the parser. -/
def resolveStructField (fieldName : String) :
    IO (List Lean.Name) := do
  let structs ← getRegisteredStructs
  pure <| structs.filterMap fun s =>
    if s.structDef.fields.any (·.name == fieldName) then
      some <| (Lean.Name.mkSimple s.structDef.name).append
        (Lean.Name.mkSimple fieldName)
    else none

/-- Look up a `defFn` short name and return the qualified
    Lean constant names (e.g.
    `"bodyPlaces" → [`Body.bodyPlaces]`) for every fn in
    scope that exposes that short name.

    Two sources are merged. (1) The runtime fn registry —
    populated by each `defFn`'s `initialize` block — covers
    cross-module references; the `initialize` blocks of an
    imported module have already executed by the time we
    elaborate code that imports it. (2) The current
    environment — fed in by the caller — covers same-module
    references: when `defFn bodyPlaces` is elaborated, it
    immediately adds the Lean constant `Body.bodyPlaces` and
    its `Body.bodyPlaces.fnDef` metadata sibling to `env`,
    but its `initialize` block won't run until the
    importing module loads. Walking env constants whose
    `fnDef`-suffixed sibling exists recovers those entries.

    Used by the `·` (method-call) parser rule to record
    gotoDef targets for method calls like `body·bodyPlaces`:
    the synthesised Lean rendering `body.bodyPlaces` carries
    no user-source position for the method token, so we
    attach a `TermInfo` leaf at the user's `bodyPlaces`
    token pointing at every matching fn constant. As with
    `resolveStructField`, multiple matches are returned so
    the LSP can offer a multi-target gotoDef when a short
    name is claimed by several `defFn`s. -/
def resolveFnByShortName (env : Lean.Environment)
    (fnName : String) : IO (List Lean.Name) := do
  let fns ← getRegisteredFns
  let fromRegistry := fns.filterMap fun f =>
    if f.fnDef.name == fnName then
      let baseName : Lean.Name := match f.fnDef.sourceNamespace with
        | some ns => Lean.Name.mkSimple ns
        | none => Lean.Name.anonymous
      some (baseName.append (Lean.Name.mkSimple fnName))
    else none
  -- Walk the env for `<X>.<fnName>.fnDef` constants the
  -- current module added but whose `initialize` registration
  -- hasn't run yet. Each match yields the parent
  -- `<X>.<fnName>` constant.
  let fromEnv : List Lean.Name :=
    env.constants.toList.filterMap fun (n, _) =>
      match n with
      | .str parent suffix =>
        if suffix == "fnDef" then
          match parent with
          | .str _ shortName =>
            if shortName == fnName then some parent else none
          | _ => none
        else none
      | _ => none
  -- De-duplicate (a fn that's in the registry might also be
  -- in env), preserving the registry order so cross-module
  -- entries appear first.
  let merged := fromRegistry ++ fromEnv.filter (fun n => !fromRegistry.contains n)
  pure merged

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

/-- Replace the first identifier token in a parsed-from-string
    syntax tree whose `Name` matches `targetName` with
    `userNameStx`. Used to graft the user's `defFn`/... name
    token (with its original source position) over the
    parsed-from-string copy that Lean's elaborator would
    otherwise emit info-tree binder leaves at — without this,
    `.ilean`'s `definition` field for the resulting constant
    points at synthetic positions inside the rendered string,
    so LSP `textDocument/definition` lands on whatever line of
    the user file happens to share those byte offsets (usually
    nowhere meaningful). -/
partial def graftUserNameToken
    (targetName : Lean.Name) (userNameStx : Lean.Syntax)
    (stx : Lean.Syntax) : Lean.Syntax :=
  match stx with
  | .ident _ _ n _ =>
    if n == targetName then userNameStx else stx
  | .node info kind args =>
    .node info kind (args.map (graftUserNameToken targetName
      userNameStx))
  | _ => stx

/-- Whether `n` resolves to the `dslProofMarker` identifier
    used as a position-grafting placeholder in DSL-rendered
    Lean source. Both the fully-qualified name and the bare
    short name are accepted, mirroring the variants
    `Lean.Name.resolveGlobalName` would emit depending on
    whether `Core.Dsl.IdentRefs` is opened in scope. -/
private def isDslProofMarkerName (n : Lean.Name) : Bool :=
  n == ``dslProofMarker || n == `dslProofMarker

/-- Whether `stx` is the parsed `Term.app` form of a
    `dslProofMarker (…)` placeholder. Returns true exactly
    when the head identifier (after stripping the leading
    function-position child) is `dslProofMarker`. -/
private def isDslProofMarkerApp (stx : Lean.Syntax) : Bool :=
  if stx.getKind != ``Lean.Parser.Term.app then false
  else
    let args := stx.getArgs
    if args.size == 0 then false
    else match args[0]! with
      | .ident _ _ n _ => isDslProofMarkerName n
      | _ => false

/-- Walk a parsed-from-string syntax tree and replace each
    `dslProofMarker (…)` application — emitted by the DSL
    renderer around every `proof[…]` body — with the next
    buffered user-source syntax (in depth-first /
    left-to-right order). Returns the rewritten syntax and the
    unconsumed tail of `userProofs`.

    Because `dslProofMarker` is a reducible identity
    (`def dslProofMarker x := x`), splicing the user-source
    proof body in place of the whole application is
    semantics-preserving: Lean's elaborator sees the proof
    term directly, against the same expected type the marker
    would have inherited from its surrounding position, and
    records `TermInfo` leaves at the user's source range — so
    the InfoView reports the expected proof goal at the user's
    `proof[…]` cursor.

    The replacement subtree is not itself recursed into, so a
    proof body that happens to contain its own
    `dslProofMarker (…)` literal would not be re-grafted —
    the DSL never emits nested markers, so this is safe. -/
partial def graftDslProofMarkers
    (userProofs : Array Lean.Syntax) (stx : Lean.Syntax)
    : Lean.Syntax × Array Lean.Syntax :=
  if isDslProofMarkerApp stx && userProofs.size > 0 then
    (userProofs[0]!, userProofs.extract 1 userProofs.size)
  else
    match stx with
    | .node info kind args =>
      let (newArgs, rest) := args.foldl
        (fun (acc, buf) child =>
          let (newChild, buf') := graftDslProofMarkers buf child
          (acc.push newChild, buf'))
        ((#[] : Array Lean.Syntax), userProofs)
      (.node info kind newArgs, rest)
    | _ => (stx, userProofs)

open Lean Elab Command in
/-- After elaborating a DSL-synthesised declaration, override
    its recorded `DeclarationRanges` so `findDeclarationRanges?`
    (and the LSP gotoDef path that consults it) lands on the
    original `defFn`/`defProperty`/... block in the user's
    source file rather than at the start of the file (which is
    where the synthetic syntax parsed from the rendered string
    ends up).

    `name` is the unqualified declaration identifier as written
    in the DSL; the current namespace is prepended to obtain
    the fully-qualified constant name registered by
    `elabCommand`. `rangeStx` is the entire user `defFn`/...
    block (typically `← getRef`); `name.raw` doubles as the
    selection range so the LSP highlights just the identifier
    when it lands on the definition.

    The `.ilean`-driven half of gotoDef (used by
    `textDocument/definition` in the LSP) is fixed
    separately by `graftUserNameToken`, which substitutes the
    user's name token into the parsed-from-string syntax
    *before* the synthesised `elabCommand` so the binder
    `TermInfo` Lean's elaborator records lands on the user's
    source position. -/
def setUserDeclRanges (name : Ident)
    (rangeStx : Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ name.getId
  Lean.Elab.addDeclarationRangesFromSyntax declName rangeStx
    name.raw

end Core.Dsl.IdentRefs
