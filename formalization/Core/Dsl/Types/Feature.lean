import Lean
import Core.Dsl.DeriveQuote

/-! # Rendering features

`Feature` is the closed enumeration of presentation-time
feature flags. A `Presentation` may opt out of selected
features via `disabledFeatures`; `defEnum` variants and
`defFn` / inline-`match` arms tagged with a disabled feature
are omitted from LaTeX rendering. Feature gating also prunes
the template-presentation appendix dependency closure (see
`Presentation/Template.lean`), so types and functions only
referenced from gated variants/arms are dropped from the
appendix rather than appearing as dangling entries. The Lean
and Rust exports ignore the `features` field — generated code
stays exhaustive.

The DSL surface accepts the upper-snake-case spelling of each
constructor (e.g. `ENUM_TYPES` for `enumTypes`); `identToFeature`
performs the mapping and raises an elaboration error on
unknown names.

**Adding a new feature:** add a constructor below *and* a
matching arm in `identToFeature`. Both edits live in this
file. -/
inductive Feature where
  | enumTypes
  | refTypes
  | aliasTypes
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited, Lean.Quote

open Lean Elab Command in
/-- Map an upper-snake-case identifier to its corresponding
    `Feature` constructor, throwing at the source position on
    an unknown spelling. The currently-supported spellings:

    * `ENUM_TYPES` → `Feature.enumTypes`
    * `REF_TYPES` → `Feature.refTypes`
    * `ALIAS_TYPES` → `Feature.aliasTypes`

    Add a new line here whenever a new constructor is added to
    `Feature`. -/
def identToFeature (id : Lean.Ident) : CommandElabM Feature := do
  match toString id.getId with
  | "ENUM_TYPES" => pure .enumTypes
  | "REF_TYPES" => pure .refTypes
  | "ALIAS_TYPES" => pure .aliasTypes
  | other =>
    Lean.throwErrorAt id
      s!"unknown feature `{other}` — \
         supported features: ENUM_TYPES, REF_TYPES, ALIAS_TYPES"

open Lean Elab Command in
/-- Map an array of feature idents (the comma-separated list
    inside a `[feature …]` prefix) to a `List Feature`. -/
def parseFeatureIdents
    (ids : Array Lean.Ident) : CommandElabM (List Feature) :=
  ids.toList.mapM identToFeature
