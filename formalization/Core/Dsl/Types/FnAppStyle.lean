/-- The notation used for function applications in the
    presentation LaTeX. -/
inductive FnAppStyle where
  /-- Rust-style call syntax: `f(a, b, c)`. -/
  | Rust
  /-- Haskell-style juxtaposition: `f a b c`. -/
  | Haskell
  deriving Repr, Inhabited, DecidableEq

/-- The function-application style used by the presentation
    LaTeX exporter. Read by `DslExpr.toDoc` when rendering
    `f(args)`-shaped call sites. -/
def PRESENTATION_FN_APP_STYLE : FnAppStyle := .Haskell

/-- The property-application style used by the presentation
    LaTeX exporter. Read when rendering applied uses of a
    `defProperty` / `defInductiveProperty` — both inside a
    property body (via `DslExpr.toDoc` with `isProperty`) and
    inside `\Require`/`\Ensure` lines (via
    `FnDef.appliedPropMath`). -/
def PRESENTATION_PROP_APP_STYLE : FnAppStyle := .Haskell
