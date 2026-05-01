import Core.Doc
import Lean

/-! # Interpolated `Doc` literals

The DSL's `defProperty` / `defFn` declarations describe themselves with
`Doc` values that are usually built by hand from `Doc.seq` chains
interleaving `Doc.plain` literal text with already-built `Doc`
arguments:

```lean
.seq [.plain "the framing instance for ",
      prDoc, .plain ", ", parDoc, .plain ", places ", pDoc,
      .plain " and ", p'Doc]
```

The `doc!` macro defined here lets the same value be written as a
single Python-style interpolated string:

```lean
doc! "the framing instance for {prDoc}, {parDoc}, places {pDoc} and {p'Doc}"
```

— literal chunks become `Doc.plain` (via the existing
`Coe String Doc := ⟨.plain⟩` instance in `Core.Doc`), and `{expr}`
holes splice in any `Doc` value (or any `String`-typed value, which
the same `Coe` instance promotes for free).

For the small handful of cases where a `.code` / `.math` interruption
is needed inside an interpolation, the abbreviations `Doc.c` and
`Doc.m` give a one-token spelling: `{Doc.c "validProgram"}`,
`{Doc.m (.bold (.raw "W"))}`. -/

namespace Doc

/-- Short alias for `Doc.code`, intended for use inside `doc!`
    interpolation holes (e.g. `{c "validProgram"}`). -/
abbrev c (s : String) : Doc := .code s

/-- Short alias for `Doc.math`, intended for use inside `doc!`
    interpolation holes (e.g. `{m (.bold (.raw "W"))}`). -/
abbrev m (md : MathDoc) : Doc := .math md

end Doc

open Lean

/-- Interpolated-string literal that desugars to a `Doc` value.

    Each literal text chunk becomes `Doc.plain "<chunk>"`; each
    `{expr}` hole becomes `(expr : Doc)`, so a `String`-valued hole
    coerces (via `Coe String Doc`) and a `Doc`-valued hole passes
    through unchanged. The whole thing is wrapped in a single
    `Doc.seq [...]`. -/
syntax (name := docInterp) "doc! " interpolatedStr(term) : term

@[macro docInterp]
def expandDocInterp : Macro := fun stx => do
  match stx with
  | `(doc! $i:interpolatedStr) =>
    let chunks := i.raw.getArgs
    let mut parts : Array (TSyntax `term) := #[]
    for chunk in chunks do
      match chunk.isInterpolatedStrLit? with
      | some str =>
        if str.isEmpty then
          continue
        let lit := Syntax.mkStrLit str
        parts := parts.push (← `((Doc.plain $lit : Doc)))
      | none =>
        let term : Term := ⟨chunk⟩
        parts := parts.push (← `(($term : Doc)))
    `(Doc.seq [$parts,*])
  | _ => Macro.throwUnsupported
