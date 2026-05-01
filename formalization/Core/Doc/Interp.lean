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

For inline code, backticks inside a literal chunk render as
`Doc.code`:

```lean
doc! "the concatenation of `edgeTargets` over every edge"
```

— produces `Doc.seq [.plain "...", .code "edgeTargets",
.plain "..."]`. A lone backtick with no closing match is left
in the prose as a literal `` ` ``.

For a `.math` interruption (no shorthand syntax), the
abbreviation `Doc.m` gives a one-token spelling:
`{Doc.m (.bold (.raw "W"))}`. The `Doc.c` alias remains
available for cases where a runtime `String` value is being
spliced as code rather than a literal string.

## Cross-reference syntax

A literal `#identifier` (or `#identifier.path`) inside a `doc!` chunk
becomes an internal hyperlink in the rendered output. For example,

```lean
doc! "Lift a PCG lifetime projection by wrapping it in \
      #PcgNode.lifetimeProjection."
```

renders the `PcgNode.lifetimeProjection` token in monospace with the
dashed underline used for intra-document links, and clicking it in the
PDF jumps to the definition.

The `#identifier` is parsed at *macro-expansion time* and emitted as
a real Lean identifier reference, so the elaborator validates the
name: a typo like `#PcgNode.fooBar` produces a Lean build error
(`unknown identifier 'PcgNode.fooBar'`) rather than a broken
hyperlink in the PDF. The link target is

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

/-- LaTeX hyperlink target for a `#`-reference. Dotted names map
    to the constructor anchor convention used by `defEnum`;
    undotted names map to the `fn:` anchor used by `defFn` /
    `defProperty`. -/
private def refTarget (ident : String) : String :=
  if ident.contains '.' then s!"#ctor:{ident}"
  else s!"#fn:{ident}"

/-- Build a `Doc.link` for a `#`-reference. The first argument is
    a placeholder whose only purpose is to force elaboration of
    the named expression — typos in the name surface as a Lean
    build error rather than a broken hyperlink. The placeholder
    is discarded at runtime. The `doc!` macro emits calls to this
    function for each `#identifier` it sees in a literal chunk. -/
def refLinkOf {α : Sort _} (_x : α) (name : String) : Doc :=
  Doc.link (.code name) (refTarget name)

end Doc

open Lean

namespace Doc.Interp

/-- A segment of a `doc!` literal chunk: a run of plain text,
    a `#identifier` cross-reference, or a backtick-delimited
    inline code span. -/
inductive ChunkSeg where
  | literal (s : String)
  | ref (parts : List String)
  | code (s : String)
  deriving Inhabited

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Greedily consume identifier-continuation characters. Returns
    the consumed prefix as a string and the remaining tail. -/
private partial def consumePart :
    List Char → String × List Char
  | [] => ("", [])
  | c :: rest =>
    if isIdentCont c then
      let (more, rest') := consumePart rest
      (String.ofList [c] ++ more, rest')
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

private def consLitChar (c : Char) : List ChunkSeg → List ChunkSeg
  | .literal p :: rest => .literal (String.ofList [c] ++ p) :: rest
  | rest => .literal (String.ofList [c]) :: rest

/-- Consume characters up to (but not including) the next
    backtick. Returns the consumed prefix and the remainder
    starting at the closing backtick, or `none` if no closing
    backtick is found. -/
private partial def consumeUntilBacktick :
    List Char → Option (String × List Char)
  | [] => none
  | '`' :: rest => some ("", '`' :: rest)
  | c :: rest =>
    (consumeUntilBacktick rest).map fun (more, after) =>
      (String.ofList [c] ++ more, after)

private partial def parseSegsAux : List Char → List ChunkSeg
  | [] => []
  | '#' :: rest =>
    let (ident, rest') := consumeRef rest
    if ident.isEmpty then
      consLitChar '#' (parseSegsAux rest)
    else
      .ref (ident.splitOn ".") :: parseSegsAux rest'
  | '`' :: rest =>
    match consumeUntilBacktick rest with
    | some (codeStr, '`' :: after) =>
      .code codeStr :: parseSegsAux after
    | _ =>
      consLitChar '`' (parseSegsAux rest)
  | c :: rest => consLitChar c (parseSegsAux rest)

/-- Split a literal `doc!` chunk into segments: `.literal` runs of
    plain text and `.ref parts` for each `#identifier`
    (or `#identifier.path`) found in the chunk. -/
def parseSegs (s : String) : List ChunkSeg :=
  parseSegsAux s.toList

end Doc.Interp

/-- Interpolated-string literal that desugars to a `Doc` value.

    Each literal text chunk is split into segments at macro-
    expansion time: runs of plain text become `Doc.plain "..."`,
    `#identifier` (or `#identifier.path`) references become
    `Doc.refLinkOf @<ident> "<name>"` — where `@<ident>` is a real
    Lean identifier reference, so the elaborator validates that
    the name resolves — and `` `text` `` spans become
    `Doc.code "text"`. Each `{expr}` hole becomes `(expr : Doc)`,
    so a `String`-valued hole coerces (via `Coe String Doc`) and a
    `Doc`-valued hole passes through unchanged. The whole thing is
    wrapped in a single `Doc.seq [...]`. -/
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
        for seg in Doc.Interp.parseSegs str do
          match seg with
          | .literal s =>
            if s.isEmpty then continue
            let lit := Syntax.mkStrLit s
            parts := parts.push (← `((Doc.plain $lit : Doc)))
          | .ref nameParts =>
            let leanName := nameParts.foldl
              (fun acc p => Name.mkStr acc p) Name.anonymous
            let ident := mkIdent leanName
            let nameStr := ".".intercalate nameParts
            let strLit := Syntax.mkStrLit nameStr
            parts := parts.push
              (← `((Doc.refLinkOf @$ident:ident $strLit : Doc)))
          | .code s =>
            if s.isEmpty then continue
            let lit := Syntax.mkStrLit s
            parts := parts.push (← `((Doc.code $lit : Doc)))
      | none =>
        let term : Term := ⟨chunk⟩
        parts := parts.push (← `(($term : Doc)))
    `(Doc.seq [$parts,*])
  | _ => Macro.throwUnsupported
