import Lean
import Core.Dsl.DeriveQuote

/-- A feature flag of the formalisation. Presentations declare
    a list of *disabled* features (default empty); DSL variants
    and match arms tagged with a disabled feature are omitted
    from LaTeX rendering. The Lean and Rust exports always emit
    every variant and arm — feature flags are presentation-only.

    The DSL surface accepts the upper-snake-case spelling of
    each constructor (e.g. `ENUM_TYPES` for `enumTypes`); the
    `parseFeatureList` helper in `DefFn` / `DefEnum` performs
    the mapping and raises an elaboration error on unknown
    names. -/
inductive Feature where
  | enumTypes
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited, Lean.Quote
