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
`{Doc.m (.bold (.raw "W"))}`.

## Cross-reference syntax

A literal `#identifier` (or `#identifier.path`) inside a `doc!` chunk
becomes an internal hyperlink in the rendered output. For example,

```lean
doc! "Lift a PCG lifetime projection by wrapping it in \
      #PcgNode.lifetimeProjection."
```

renders the `PcgNode.lifetimeProjection` token in monospace with the
dashed underline used for intra-document links, and clicking it in the
PDF jumps to the definition. The reference target is

- `ctor:<TypeName>.<CtorName>` for a dotted name (matches the
  `\hypertarget{ctor:...}{}` anchors emitted by `defEnum` for each
  variant), and
- `fn:<name>` for an undotted name (matches `\hypertarget{fn:...}{}`
  anchors emitted by `defFn` and `defProperty`).

A `#` not followed by an identifier-start character is left as a
literal `#` in the prose. -/

namespace Doc

/-- Short alias for `Doc.code`, intended for use inside `doc!`
    interpolation holes (e.g. `{c "validProgram"}`). -/
abbrev c (s : String) : Doc := .code s

/-- Short alias for `Doc.math`, intended for use inside `doc!`
    interpolation holes (e.g. `{m (.bold (.raw "W"))}`). -/
abbrev m (md : MathDoc) : Doc := .math md

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Greedily consume identifier-continuation characters, returning
    the consumed prefix as a string and the remaining tail. -/
private partial def consumePart :
    List Char → String × List Char
  | [] => ("", [])
  | c :: rest =>
    if isIdentCont c then
      let (more, rest') := consumePart rest
      (String.mk [c] ++ more, rest')
    else ("", c :: rest)

/-- After an identifier head has been consumed, fold any
    `.<identStart><identCont>*` continuations into the same dotted
    name. A trailing `.` not followed by an identifier-start
    character (e.g. a sentence-ending period) is left in the input
    so it is preserved as literal prose. -/
private partial def consumeDottedTail :
    String × List Char → String × List Char
  | (cur, '.' :: c :: rest) =>
    if isIdentStart c then
      let (more, rest') := consumePart (c :: rest)
      consumeDottedTail (cur ++ "." ++ more, rest')
    else (cur, '.' :: c :: rest)
  | acc => acc

/-- Try to consume a (possibly dotted) identifier from the head of
    `cs`. Returns `("", cs)` if `cs` does not start with an
    identifier-start character. -/
private def consumeRef (cs : List Char) : String × List Char :=
  match cs with
  | [] => ("", [])
  | c :: rest =>
    if !isIdentStart c then ("", c :: rest)
    else
      let (first, after1) := consumePart (c :: rest)
      consumeDottedTail (first, after1)

/-- LaTeX hyperlink target for a `#`-reference. Dotted names map
    to the constructor anchor convention used by `defEnum`;
    undotted names map to the `fn:` anchor used by `defFn` /
    `defProperty`. -/
private def refTarget (ident : String) : String :=
  if ident.contains '.' then s!"#ctor:{ident}"
  else s!"#fn:{ident}"

private def consLit (c : Char) : List Doc → List Doc
  | .plain p :: rest => .plain (String.mk [c] ++ p) :: rest
  | rest => .plain (String.mk [c]) :: rest

private partial def parseLinksAux : List Char → List Doc
  | [] => []
  | '#' :: rest =>
    let (ident, rest') := consumeRef rest
    if ident.isEmpty then
      consLit '#' (parseLinksAux rest)
    else
      .link (.code ident) (refTarget ident) :: parseLinksAux rest'
  | c :: rest => consLit c (parseLinksAux rest)

/-- Parse a literal `doc!` chunk into a `Doc`, expanding
    `#identifier` (and `#identifier.path`) into `Doc.link`
    hyperlinks. Returns a single `.plain s` when the chunk
    contains no references. -/
def parseLinks (s : String) : Doc :=
  match parseLinksAux s.toList with
  | [] => .plain ""
  | [d] => d
  | ds => .seq ds

end Doc

open Lean

/-- Interpolated-string literal that desugars to a `Doc` value.

    Each literal text chunk is parsed by `Doc.parseLinks` so any
    `#identifier` patterns become `Doc.link` hyperlinks (see the
    file docstring); chunks without `#`-references just produce
    `Doc.plain "<chunk>"`. Each `{expr}` hole becomes
    `(expr : Doc)`, so a `String`-valued hole coerces (via
    `Coe String Doc`) and a `Doc`-valued hole passes through
    unchanged. The whole thing is wrapped in a single
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
        parts := parts.push (← `((Doc.parseLinks $lit : Doc)))
      | none =>
        let term : Term := ⟨chunk⟩
        parts := parts.push (← `(($term : Doc)))
    `(Doc.seq [$parts,*])
  | _ => Macro.throwUnsupported
