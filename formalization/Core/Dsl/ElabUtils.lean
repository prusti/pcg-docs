import Core.Registry
import Core.Dsl.DslType
import Core.Dsl.Types.Feature
import Lean

/-! # Shared elaboration helpers for DSL `def…` commands

Centralises a handful of helpers that the individual `def…`
elaborators (`DefAlias`, `DefEnum`, `DefStruct`, `DefFn`,
`DefProperty`, `DefInductiveProperty`) all need:

* `Syntax.toTypeStr` — the canonical Lean-source rendering of
  a type-position `Syntax`. Handles the bare-ident special
  case and falls back to `reprint` (or `toString`) for
  compound forms.
* `typeParamNames` — flatten an optional `{P Q …}` ident array
  into the equivalent `List String`.
* `defaultDerives` — the default `deriving` ident array
  (`DecidableEq`, `Repr`, `Hashable`).
* `usesHashPropagating` — decide whether a list of field/arg
  type strings drags `BEq`/`Hashable` constraints onto the
  declaring type's parameters (because they reference `Map`,
  `Set`, or a previously-recorded propagating type).
* `mkTypeParamBinders` — build the `(P : Type) [BEq P] …`
  bracketed-binder array used by generic `defStruct` /
  `defEnum`.
* `registerInCurrentModule` — emit the `initialize register…`
  command that records a freshly-defined registry entry.

Keeping all of these in one place removes the same-shape
duplication that previously sat in `DefStruct.lean` and
`DefEnum.lean` (and let smaller copies drift in `DefFn`,
`DefAlias`, and friends). -/

namespace Core.Dsl.ElabUtils

open Lean Elab Command

/-- The canonical Lean-source rendering of a type-position
    `Syntax`. Bare idents return their unqualified name; every
    other shape falls back to `reprint` (which handles
    parenthesised forms, generic applications, etc.) and
    finally to `toString` if `reprint` declines. -/
def toTypeStr (stx : Syntax) : String :=
  if stx.isIdent then toString stx.getId
  else stx.reprint.getD (toString stx)

/-- `toTypeStr`, additionally trimming surrounding ASCII
    whitespace. Used by the `def…` commands that splice the
    type string into a generated Lean source expression where
    leading/trailing space would be ugly. -/
def toTypeStrTrimmed (stx : Syntax) : String :=
  (toTypeStr stx).trimAscii.toString

/-- Flatten `{P Q …}` into `["P", "Q", …]`; the absent
    optional yields `[]`. -/
def typeParamNames
    (tps : Option (TSyntaxArray `ident)) : List String :=
  match tps with
  | some ids => ids.toList.map (toString ·.getId)
  | none => []

/-- Render a type-parameter name list as the
    `" (P : Type) (Q : Type) …"` chunk spliced into the
    generated `abbrev`/`inductive` source. Empty input yields
    the empty string (no leading space). -/
def renderTypeParamSig (params : List String) : String :=
  if params.isEmpty then ""
  else " " ++ " ".intercalate
    (params.map fun p => s!"({p} : Type)")

/-- The default `deriving` instance list used by `defEnum` /
    `defStruct` when the user omits `deriving …`. -/
def defaultDerives : Array Ident :=
  #[mkIdent ``DecidableEq, mkIdent ``Repr, mkIdent ``Hashable]

/-- Top-level identifiers in `s` (whitespace-separated, with
    parens flattened to whitespace). For instance,
    `"Option (Set P)"` becomes `["Option", "Set", "P"]`. -/
private def typeTokens (s : String) : List String :=
  let chars := s.toList.map fun c =>
    if c == '(' || c == ')' then ' ' else c
  String.ofList chars
    |>.splitOn " "
    |>.filter (· != "")

/-- Whether any string in `tyStrs` drags `BEq`/`Hashable`
    constraints onto a generic type's parameters. A type does
    so when it (transitively) mentions `Map`, `Set`, or any
    type previously recorded via `registerHashPropagating`. -/
def usesHashPropagating (tyStrs : List String) : IO Bool := do
  let propagating ← hashPropagatingTypes.get
  return tyStrs.any fun s =>
    typeTokens s |>.any fun tok =>
      tok == "Map" || tok == "Set" || propagating.contains tok

/-- Build the `(P : Type)` (and, when `withHashConstraints`,
    `[BEq P] [Hashable P]`) bracketed-binder array for each
    name in `paramNames`. Used by both `defEnum` and
    `defStruct` for the generic-type case. -/
def mkTypeParamBinders
    (paramNames : List String)
    (withHashConstraints : Bool)
    : CommandElabM
        (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :=
  paramNames.toArray.foldlM (init := #[]) fun acc p => do
    let pId := mkIdent (Name.mkSimple p)
    let typeBinder ← `(Lean.Parser.Term.bracketedBinderF|
      ($pId : Type))
    if withHashConstraints then
      let beq ← `(Lean.Parser.Term.bracketedBinderF| [BEq $pId])
      let hash ← `(Lean.Parser.Term.bracketedBinderF|
        [Hashable $pId])
      pure (acc.push typeBinder |>.push beq |>.push hash)
    else
      pure (acc.push typeBinder)

/-- Emit `initialize <registerFn> <defId> <currentModule>` so
    a freshly-defined `<X>.<defId>` registry entry survives
    across module loads. The `register…` argument is the
    fully-qualified name of the registry's `register…`
    function (e.g. `Core.registerStructDef`); `defId` is the
    DSL-generated registry-entry constant. -/
def registerInCurrentModule
    (registerFn : Name) (defId : Ident) : CommandElabM Unit := do
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  let regIdent := mkIdent registerFn
  elabCommand (← `(command|
    initialize ($regIdent $defId $modName)))

/-- Map an upper-snake-case identifier to its corresponding
    `Feature` constructor, throwing at the source position on
    an unknown spelling. The currently-supported spellings:

    * `ENUM_TYPES` → `Feature.enumTypes`

    Add a new line here whenever a new constructor is added to
    `Feature`. -/
def identToFeature (id : Lean.Ident) : CommandElabM Feature := do
  match toString id.getId with
  | "ENUM_TYPES" => pure .enumTypes
  | other =>
    Lean.throwErrorAt id
      s!"unknown feature `{other}` — \
         supported features: ENUM_TYPES"

/-- Map an array of feature idents (the comma-separated list
    inside a `[feature …]` prefix) to a `List Feature`. -/
def parseFeatureIdents
    (ids : Array Lean.Ident) : CommandElabM (List Feature) :=
  ids.toList.mapM identToFeature

end Core.Dsl.ElabUtils
