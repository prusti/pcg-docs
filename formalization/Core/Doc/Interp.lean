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
literal `#` in the prose.

For labels that fall outside the `#name` form's accepted set —
e.g. ones that need to abut surrounding prose without a terminator
— the bracketed `#[name]` form takes any characters up to the
closing `]`:

```lean
doc! "Pointer #[m'->next] is owned by #[ProjectionElem.Field]'s parent"
```

The bracketed body is *not* validated as a Lean identifier (the
elaborator does not push a `@<ident>` reference for it), so typos
surface only as broken hyperlinks at render time, not as compile
errors.

## Italic and bold shorthand

`_X_` produces italic content; `__X__` produces bold. Both
forms also work inside a `$...$` math block:

```lean
doc! "An allocation $_alpha_ ∈ _Allocation_$ is __live__ when…"
```

renders as:

* `_alpha_` / `_Allocation_` → `\mathit{alpha}` / `\mathit{Allocation}`
  in math mode, or `\textit{...}` in text mode (outside `$...$`);
* `__live__` → `\textbf{live}` in text mode, or `\mathbf{live}` in math mode.

The body must be non-empty and may not contain `$`; bodies inside
`__X__` may not contain `_` either (`_X_X_` is therefore parsed as
two italic spans, not as a bold span). The bold case is matched
*before* italic in the parser, so `__X__` always wins over a
hypothetical `_(_X_)_`. -/

namespace Doc

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

/-- Like `refLinkOf` but takes the name as a `String` only — no
    compile-time validation that the identifier resolves. Use
    only for forward references that can't be expressed with
    `refLinkOf`'s `@<ident>` argument due to definition order
    (e.g. a helper whose doc references the higher-level function
    it is called from, where adding the import or moving the
    decl would create a cycle).

    The banned-pattern lint matches `Doc.code` directly, so calls
    to this function are exempt — their head is `Doc.refLinkByName`
    rather than `Doc.code` — which is also why this function is
    intentionally one-shot rather than reused: the `_` arg of
    `refLinkOf` exists to provide validation, and there's no way
    to opt out per-call without giving up that validation. -/
def refLinkByName (name : String) : Doc :=
  Doc.link (.code name) (refTarget name)

end Doc

open Lean

namespace Doc.Interp

/-- A segment of a math sub-chunk inside a `$...$` block of a
    `doc!` literal. `mathLit` carries already-translated LaTeX
    (Unicode math characters that don't have a matching
    `MathSym` are mapped to `\doteq` etc. at parse time);
    `mathSym` carries the unqualified name of a `MathSym`
    constructor that the unicode char *did* match (so the
    char can render via the structured `MathDoc.sym` path,
    which bypasses the multi-character `\mathit{…}`
    auto-wrap that `MathDoc.raw` performs on text); `mathRef`
    carries a `#identifier` reference, rendered in math text
    mode; `mathBold` carries the body of a `__X__` span and
    renders as `MathDoc.bold (MathDoc.raw "X")`; `mathItalic`
    carries the body of a `_X_` span and renders as
    `MathDoc.raw "X"` (which is already `\mathit{X}` for
    multi-character bodies thanks to the LatexMath escaping
    rule, and a single character is auto-italicised by math
    mode itself). -/
inductive MathChunkSeg where
  | mathLit (s : String)
  | mathSym (symName : String)
  | mathRef (name : String)
  | mathBold (s : String)
  | mathItalic (s : String)
  deriving Inhabited

/-- A segment of a `doc!` literal chunk: a run of plain text,
    a `#identifier` cross-reference, a `#{name}` braced
    cross-reference, a backtick-delimited inline code span,
    a `__X__` bold-text span, or a `$...$` math block.

    `ref` carries the byte offsets of its `#identifier`
    substring relative to the start of the (decoded) chunk
    string — `startOff` points at the `#`, `endOff` points
    one byte past the last identifier character. The macro
    uses these offsets to attach `SourceInfo.original` to the
    synthesised `Syntax.ident`, so the language server can
    treat the substring as a real identifier reference for
    goto-definition, hover, and semantic highlighting.

    `refByName` is the bracket-delimited `#[name]` form: it
    lets the source spell a label whose characters fall
    outside the unbracketed `#name` form's accepted set
    (anything beyond Lean's `isIdRest` plus dotted segments)
    or that needs to abut surrounding prose without a
    terminator (`#[name]'s` keeps the `'s` outside the
    label). The label is treated as an *unvalidated* string —
    the elaborator does not try to resolve it as a
    `@<ident>` reference, so typos surface only at render
    time, not at compile time. Square brackets were chosen
    so the form needs no escaping inside an interpolated
    string literal (curly braces would collide with `doc!`'s
    `{expr}` interpolation syntax).

    `mathBlock` carries the segments of the `$...$` content —
    plain text inside math is Unicode-translated to LaTeX
    commands (e.g. `≐` → `\doteq`) at parse time, and
    `#identifier` / `#[name]` references inside math become
    text-mode name renderings. A `__X__` span inside a
    `$...$` block becomes a `MathChunkSeg.mathBold` segment
    rendered as `MathDoc.bold (.raw "X")`.

    `bold` is the same `__X__` form encountered *outside* a
    math block; it carries the body verbatim and renders as
    `Doc.bold (.plain "X")`. The body of either form must be
    non-empty and contain neither `_` nor `$`, so the shorthand
    stays a tight match for the single-token cases the codebase
    actually uses (e.g. `D`, `E`, `R`, `S`, `U`, `W`, `e`, `n`,
    `n+1`); anything else falls back to literal characters
    (text mode) or the regular math segment list (math mode).
    The same source spelling `__X__` therefore acts as
    `MathDoc.bold` inside `$...$` and `Doc.bold` everywhere
    else, so `$__X__$` is just `$...$` wrapping `__X__`.

    `italic` is the `_X_` (single-underscore) sibling of
    `bold`: outside a `$...$` block it carries the body
    verbatim and renders as `Doc.italic (.plain "X")`, which
    is `\textit{X}` in LaTeX text mode; inside a `$...$`
    block (where the body is captured as
    `MathChunkSeg.mathItalic` instead) it renders as
    `MathDoc.italic (MathDoc.raw "X")`, i.e. `\mathit{X}`.
    The body shape rules match `bold`: non-empty and no `$`.
    The bold case is matched *before* italic in the parser,
    so `__X__` always wins over a hypothetical `_(_X_)_`. -/
inductive ChunkSeg where
  | literal (s : String)
  | ref (parts : List String) (startOff endOff : Nat)
  | refByName (name : String)
  | code (s : String)
  | mathBlock (segs : List MathChunkSeg)
  | bold (s : String)
  | italic (s : String)
  deriving Inhabited

/-- Map a Unicode math character to a `MathSym` constructor
    name when one applies. The structured `MathSym` route
    renders via `LatexMath.raw` (no `\mathit{…}` auto-wrap)
    and also stays meaningful for the Typst / HTML backends,
    which translate each `MathSym` separately. Returns
    `none` for characters that have no `MathSym` equivalent;
    callers fall back to `unicodeMathToLatex` for those. -/
def unicodeMathToSym (c : Char) : Option String :=
  match c with
  | '∈' => some "setContains"
  | '≤' => some "le"
  | '≠' => some "neq"
  | '∧' => some "land"
  | '∨' => some "lor"
  | '→' => some "implies"
  | '⇒' => some "fatArrow"
  | '∀' => some "forall_"
  | '∃' => some "exists_"
  | '∅' => some "emptySet"
  | '↦' => some "mapsto"
  | '⟨' => some "langle"
  | '⟩' => some "rangle"
  | '⊥' => some "bot"
  | '⊤' => some "top"
  | '∪' => some "cup"
  | '∩' => some "cap"
  | 'π' => some "pi"
  | 'μ' => some "mu"
  | 'α' => some "alpha"
  | 'θ' => some "theta"
  -- `ϕ` (U+03D5, GREEK PHI SYMBOL) is the loopy form rendered
  -- by `\phi`; `φ` (U+03C6, GREEK SMALL LETTER PHI) is the
  -- curly form rendered by `\varphi`.
  | 'ϕ' => some "phi"
  | 'φ' => some "varphi"
  | _ => none

/-- Map a Unicode math character to its raw LaTeX command
    form. Used as a fallback for characters that don't have a
    `MathSym` equivalent (`unicodeMathToSym` returns `none`).
    Each translation is followed by `{}` so the command stays
    a separate token from a following alphabetic character —
    e.g. `≐y` becomes `\doteq{}y` rather than the undefined
    `\doteqy`. The trailing `{}` is invisible in the common
    case where the user writes a space around the operator.
    Note: text emitted via this fallback ends up wrapped in
    `\mathit{…}` by the `MathDoc.raw → LatexMath.escaped`
    lowering when it accumulates with neighbouring literal
    characters, since the resulting `mathLit` segment has
    length > 1; that's a known wart for the chars handled
    here (e.g. `≐`) but the math-mode visual is acceptable. -/
def unicodeMathToLatex (c : Char) : Option String :=
  match c with
  | '≐' => some "\\doteq{}"
  | '≥' => some "\\ge{}"
  | '∉' => some "\\notin{}"
  | _ => none

private def renderMathChar (c : Char) : String :=
  unicodeMathToLatex c |>.getD (String.ofList [c])

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Accepted continuation characters for the unbracketed
    `#name` form. Mirrors Lean's `String.isIdRest` to the
    extent that matters here: alphanumerics, `_`, and `'` (so
    primed names like `m'` round-trip without needing the
    bracketed `#[m']` form). `!` / `?` are deliberately *not*
    accepted; they're commonly punctuation in prose, and the
    bracketed form is available when they're really part of
    the identifier. -/
private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

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
    identifier-start character. Shared with the `presBody!`
    chunk parser, which uses it to match `[[Name]]` bodies. -/
def consumeRef (cs : List Char) : String × List Char :=
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

private def consMathLitStr (s : String) :
    List MathChunkSeg → List MathChunkSeg
  | .mathLit p :: rest => .mathLit (s ++ p) :: rest
  | rest => .mathLit s :: rest

/-- Consume characters up to (and consuming) the next `]`.
    Returns the inner text and the remainder *after* the
    closing bracket, or `none` if no closing bracket is found.
    Used to parse the body of a `#[name]` bracketed reference,
    which lets a source label include characters that are
    not accepted by the unbracketed `#name` form (or that
    need to abut surrounding prose without a terminator). -/
private partial def consumeUntilRBracket :
    List Char → Option (String × List Char)
  | [] => none
  | ']' :: rest => some ("", rest)
  | c :: rest =>
    (consumeUntilRBracket rest).map fun (more, after) =>
      (String.ofList [c] ++ more, after)

/-- Read the body of a `__X__` bold span whose opening `__`
    has already been consumed. Accepts characters up to a
    closing `__`, but rejects bodies that contain `_` or `$`
    (so the shorthand stays a tight match for the cases the
    codebase actually uses — single tokens like `U`, `E`, `n`,
    `n+1`). Returns the consumed body and the remainder after
    the closing `__`, or `none` to defer to the surrounding
    parser (which then treats the leading `__` as literal). -/
private partial def consumeBoldBody :
    List Char → List Char →
    Option (String × List Char)
  | acc, '_' :: '_' :: rest =>
    if acc.isEmpty then none
    else some (String.ofList acc.reverse, rest)
  | _, '_' :: _ => none
  | _, '$' :: _ => none
  | _, [] => none
  | acc, c :: rest => consumeBoldBody (c :: acc) rest

/-- Read the body of a `_X_` italic span whose opening `_`
    has already been consumed. Accepts characters up to the
    next `_`, but rejects bodies that contain `$`. The body
    must be non-empty. Returns the consumed body and the
    remainder after the closing `_`, or `none` to defer to the
    surrounding parser (which then treats the leading `_` as
    literal). -/
private partial def consumeItalicBody :
    List Char → List Char →
    Option (String × List Char)
  | acc, '_' :: rest =>
    if acc.isEmpty then none
    else some (String.ofList acc.reverse, rest)
  | _, '$' :: _ => none
  | _, [] => none
  | acc, c :: rest => consumeItalicBody (c :: acc) rest

/-- Parse the body of a `$...$` math block. Returns the parsed
    segments, the remainder after the closing `$`, and whether
    a closing `$` was actually found. If unclosed, the caller
    treats the opening `$` as a literal. -/
private partial def parseMathSegsAux :
    List Char → List MathChunkSeg × List Char × Bool
  | [] => ([], [], false)
  | '$' :: rest => ([], rest, true)
  | '_' :: '_' :: rest =>
    -- `__X__` inside a `$...$` math block: emit a `mathBold`
    -- segment (rendered as `MathDoc.bold (.raw "X")`). Falls
    -- back to literal underscores when the body is empty or
    -- contains `_`/`$`.
    match consumeBoldBody [] rest with
    | some (name, after) =>
      let (more, restFinal, closed) := parseMathSegsAux after
      (.mathBold name :: more, restFinal, closed)
    | none =>
      let (more, restFinal, closed) := parseMathSegsAux rest
      (consMathLitStr "__" more, restFinal, closed)
  | '_' :: rest =>
    -- `_X_` inside a `$...$` math block: emit a `mathItalic`
    -- segment (rendered as `MathDoc.italic (.raw "X")`,
    -- which is `\mathit{X}` in LaTeX). Falls back to a literal
    -- underscore when the body is empty or contains `$`. The
    -- bold case above is matched first so `__X__` always wins.
    match consumeItalicBody [] rest with
    | some (name, after) =>
      let (more, restFinal, closed) := parseMathSegsAux after
      (.mathItalic name :: more, restFinal, closed)
    | none =>
      let (more, restFinal, closed) := parseMathSegsAux rest
      (consMathLitStr "_" more, restFinal, closed)
  | '#' :: '[' :: rest =>
    -- `#[name]` form: any chars up to the closing `]` form
    -- the name. Falls back to a literal `#` when no closing
    -- bracket is found, or when the bracket pair is empty.
    match consumeUntilRBracket rest with
    | some (name, after) =>
      if name.isEmpty then
        let (more, restFinal, closed) :=
          parseMathSegsAux ('[' :: rest)
        (consMathLitStr "#" more, restFinal, closed)
      else
        let (more, restFinal, closed) := parseMathSegsAux after
        (.mathRef name :: more, restFinal, closed)
    | none =>
      let (more, restFinal, closed) :=
        parseMathSegsAux ('[' :: rest)
      (consMathLitStr "#" more, restFinal, closed)
  | '#' :: rest =>
    match rest with
    | c :: rest' =>
      if isIdentStart c then
        let (name, after) := consumePart (c :: rest')
        let (more, restFinal, closed) := parseMathSegsAux after
        (.mathRef name :: more, restFinal, closed)
      else
        let (more, restFinal, closed) := parseMathSegsAux rest
        (consMathLitStr "#" more, restFinal, closed)
    | [] => ([.mathLit "#"], [], false)
  | c :: rest =>
    let (more, restFinal, closed) := parseMathSegsAux rest
    match unicodeMathToSym c with
    | some symName =>
      -- Unicode char with a structured `MathSym` equivalent:
      -- emit it as a separate `mathSym` segment. This keeps
      -- it from getting auto-wrapped in `\mathit{…}` along
      -- with any neighbouring literal characters (the
      -- multi-character `mathLit " ∈ "` accumulator would
      -- otherwise lower to `LatexMath.escaped " \in{} "`
      -- and then to `\mathit{ \in{} }`).
      (.mathSym symName :: more, restFinal, closed)
    | none =>
      (consMathLitStr (renderMathChar c) more, restFinal, closed)

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
  | '_' :: '_' :: rest =>
    -- `__X__` outside a math block: emit a `bold` segment
    -- (rendered as `Doc.bold (.plain "X")`). Falls back to
    -- literal underscores when the body is empty or contains
    -- `_`/`$`.
    match consumeBoldBody [] rest with
    | some (name, after) =>
      .bold name :: parseSegsAux after
    | none =>
      consLitChar '_' (consLitChar '_' (parseSegsAux rest))
  | '_' :: rest =>
    -- `_X_` outside a math block: emit an `italic` segment
    -- (rendered as `Doc.italic (.plain "X")`). Falls back to
    -- a literal underscore when the body is empty or contains
    -- `$`. The bold case above is matched first so `__X__`
    -- always wins.
    match consumeItalicBody [] rest with
    | some (name, after) =>
      .italic name :: parseSegsAux after
    | none =>
      consLitChar '_' (parseSegsAux rest)
  | '$' :: rest =>
    let (segs, rest', closed) := parseMathSegsAux rest
    if closed then
      .mathBlock segs :: parseSegsAux rest'
    else
      consLitChar '$' (parseSegsAux rest)
  | '#' :: '[' :: rest =>
    -- `#[name]` form: any chars up to the closing `]` form
    -- the name. The body is treated as an unvalidated label
    -- (no `@<ident>` resolution), so it can contain
    -- characters not accepted by the unbracketed form, or
    -- abut surrounding prose without a terminator (e.g.
    -- `#[name]'s` keeps the `'s` outside the label). Falls
    -- back to a literal `#` when no closing bracket is found
    -- or the bracket pair is empty.
    match consumeUntilRBracket rest with
    | some (name, after) =>
      if name.isEmpty then
        consLitChar '#' (parseSegsAux ('[' :: rest))
      else
        .refByName name :: parseSegsAux after
    | none =>
      consLitChar '#' (parseSegsAux ('[' :: rest))
  | '#' :: rest =>
    let (ident, rest') := consumeRef rest
    if ident.isEmpty then
      consLitChar '#' (parseSegsAux rest)
    else
      -- Offsets are filled in by `parseSegs`'s annotation pass.
      .ref (ident.splitOn ".") 0 0 :: parseSegsAux rest'
  | '`' :: rest =>
    match consumeUntilBacktick rest with
    | some (codeStr, '`' :: after) =>
      .code codeStr :: parseSegsAux after
    | _ =>
      consLitChar '`' (parseSegsAux rest)
  | c :: rest =>
    -- A Unicode math character with a known `MathSym` name —
    -- e.g. `∅` / `∪` / `∩` — that appears outside any `$…$`
    -- block is rendered as a one-segment math block, just as
    -- if it had been written `$∅$`. Without this, the
    -- character would coerce through `Doc.plain` and reach
    -- LaTeX as a Unicode literal, which leaves authors
    -- writing the more verbose `{Doc.m (.sym .emptySet)}`
    -- interpolation hole instead. The `MathDoc.seq` wrap
    -- mirrors how a `$…$` block lowers and lets the
    -- banned-pattern checker distinguish the auto-wrapped
    -- form from a hand-written `Doc.math (MathDoc.sym …)`.
    match unicodeMathToSym c with
    | some symName =>
      .mathBlock [.mathSym symName] :: parseSegsAux rest
    | none => consLitChar c (parseSegsAux rest)

/-- Annotate each `.ref` segment with the byte offset of its
    `#identifier` substring inside the decoded chunk string.

    Each segment consumes a known number of bytes from the
    original chunk: `.literal s` consumes `s.utf8ByteSize`
    (the parser builds the literal from the consumed source
    chars verbatim), `.ref parts` consumes `1 +
    intercalated.utf8ByteSize` (a leading `#` plus the dotted
    name), and `.code s` consumes `2 + s.utf8ByteSize` (the
    pair of backticks). `.mathBlock` segments hold the
    *translated* LaTeX form of the source characters and so
    can't be sized from the stored string; we don't track
    per-segment offsets inside math blocks (no goto-def
    support there yet) and only charge an opaque advance for
    the surrounding `$...$` delimiters. Walking the segment
    list and summing these per-segment widths gives a running
    offset that is the byte position of each segment's start
    in the decoded chunk. -/
private def annotateOffsets : List ChunkSeg → Nat → List ChunkSeg
  | [], _ => []
  | .literal t :: rest, off =>
    .literal t :: annotateOffsets rest (off + t.utf8ByteSize)
  | .ref parts _ _ :: rest, off =>
    let identLen := (".".intercalate parts).utf8ByteSize
    let endOff := off + 1 + identLen
    .ref parts off endOff :: annotateOffsets rest endOff
  | .refByName name :: rest, off =>
    -- Source bytes consumed by the `#[name]` form: `#[` +
    -- the name's bytes + `]`.
    .refByName name ::
      annotateOffsets rest (off + 3 + name.utf8ByteSize)
  | .code t :: rest, off =>
    .code t :: annotateOffsets rest (off + 2 + t.utf8ByteSize)
  | .mathBlock segs :: rest, off =>
    .mathBlock segs :: annotateOffsets rest (off + 2)
  | .bold s :: rest, off =>
    -- Source bytes consumed by the `__X__` form: leading
    -- `__` (2) + body bytes + trailing `__` (2).
    .bold s :: annotateOffsets rest (off + 4 + s.utf8ByteSize)
  | .italic s :: rest, off =>
    -- Source bytes consumed by the `_X_` form: leading
    -- `_` (1) + body bytes + trailing `_` (1).
    .italic s :: annotateOffsets rest (off + 2 + s.utf8ByteSize)

/-- Split a literal `doc!` chunk into segments: `.literal` runs of
    plain text, `.ref parts startOff endOff` for each
    `#identifier` (or `#identifier.path`) found in the chunk
    (with byte offsets in the decoded chunk string), and
    `.code s` for each backtick-delimited inline code span. -/
def parseSegs (s : String) : List ChunkSeg :=
  annotateOffsets (parseSegsAux s.toList) 0

/-- Parse an entire string as math content (the same grammar as
    the body of a `$...$` block in `doc!`). Differs from the
    `$...$` parse only at the boundary: a stray `$` inside the
    string is treated as a literal character (since there is no
    enclosing math delimiter to terminate). Used by the
    `mathdoc!` macro to share its parser with `doc!`. -/
partial def parseMathString (s : String) : List MathChunkSeg :=
  let rec loop (chars : List Char) : List MathChunkSeg :=
    match chars with
    | [] => []
    | _ =>
      let (segs, rest, closed) := parseMathSegsAux chars
      if closed then segs ++ consMathLitStr "$" (loop rest)
      else segs
  loop s.toList

end Doc.Interp

open Lean Elab Term in
/-- Build a `MathDoc.seq` term from a list of math segments.
    Shared by the `$...$` case in `doc!` and the `mathdoc!`
    macro: a stable mapping from each `MathChunkSeg` variant to
    the corresponding `MathDoc` constructor. -/
def Doc.Interp.mathSegsToTerm (segs : List Doc.Interp.MathChunkSeg) :
    TermElabM (TSyntax `term) := do
  let mut mdParts : Array (TSyntax `term) := #[]
  for s in segs do
    match s with
    | .mathLit t =>
      if t.isEmpty then continue
      let lit := Syntax.mkStrLit t
      mdParts := mdParts.push (← `(MathDoc.raw $lit))
    | .mathSym symName =>
      let symId := mkIdent (Name.mkSimple symName)
      mdParts := mdParts.push (← `(MathDoc.sym .$symId))
    | .mathRef name =>
      let lit := Syntax.mkStrLit name
      mdParts := mdParts.push (← `(MathDoc.text $lit))
    | .mathBold t =>
      let lit := Syntax.mkStrLit t
      mdParts := mdParts.push
        (← `(MathDoc.bold (MathDoc.raw $lit)))
    | .mathItalic t =>
      -- `_X_` inside math content lowers to `MathDoc.raw X`:
      -- the LatexMath renderer already wraps multi-character
      -- `escaped` strings in `\mathit{...}` (and a single
      -- character is auto-italicised by math mode itself), so
      -- explicit `MathDoc.italic` would double-wrap as
      -- `\mathit{\mathit{X}}`.
      let lit := Syntax.mkStrLit t
      mdParts := mdParts.push (← `(MathDoc.raw $lit))
  `(MathDoc.seq [$mdParts,*])

/-- Interpolated-string literal that desugars to a `Doc` value.

    Each literal text chunk is split into segments at
    elaboration time: runs of plain text become `Doc.plain "..."`,
    `#identifier` (or `#identifier.path`) references become
    `Doc.refLinkOf @<ident> "<name>"` — where `@<ident>` is a real
    Lean identifier reference, so the elaborator validates that
    the name resolves — and `` `text` `` spans become
    `Doc.code "text"`. Each `{expr}` hole becomes `(expr : Doc)`,
    so a `String`-valued hole coerces (via `Coe String Doc`) and a
    `Doc`-valued hole passes through unchanged. The whole thing is
    wrapped in a single `Doc.seq [...]`.

    Implemented as a `term_elab` rather than a `macro` so the
    `#identifier` substrings can have explicit `TermInfo` nodes
    pushed into the elaboration `InfoTree` at their absolute
    source ranges. The Lean language server's
    `collectInfoBasedSemanticTokens` walks the `InfoTree` and
    emits a semantic-highlight token for each `TermInfo` whose
    `Syntax` carries `SourceInfo.original` — pushing those
    leaves manually is what makes `#refs` render as identifier
    tokens (rather than plain string text) in VS Code, and is
    what enables hover / goto-def to fire on the substring. -/
syntax (name := docInterp) "doc! " interpolatedStr(term) : term

open Lean Elab Term in
/-- Lower a list of `ChunkSeg`s — the inline-grammar segments
    produced by `parseSegs` — into an array of `Doc`-typed
    Lean term syntax. The result is intended to be inserted
    into a surrounding `Doc.seq [...]` (or interleaved with
    other Doc-typed terms produced by the caller).
    `chunkPos?` is the source position of the chunk's leading
    delimiter (used to wire `SourceInfo.original` onto
    `#identifier` `Syntax.ident`s so the LSP can resolve them
    for goto-def / hover / semantic highlighting).
    Shared by the `doc!` and `presBody!` elaborators. -/
def Doc.Interp.chunkSegsToDocTerms
    (chunkPos? : Option String.Pos.Raw) (segs : List ChunkSeg) :
    TermElabM (Array (TSyntax `term)) := do
  let mut parts : Array (TSyntax `term) := #[]
  for seg in segs do
    match seg with
    | .literal s =>
      if s.isEmpty then continue
      let lit := Syntax.mkStrLit s
      parts := parts.push (← `((Doc.plain $lit : Doc)))
    | .ref nameParts startOff endOff =>
      let leanName := nameParts.foldl
        (fun acc p => Name.mkStr acc p) Name.anonymous
      let nameStr := ".".intercalate nameParts
      -- Build the synthesised `Syntax.ident` with
      -- `SourceInfo.original` pointing at the
      -- `#identifier` substring's absolute file
      -- position. With this info the LSP can resolve
      -- the substring back to a known identifier for
      -- goto-def, hover, and (after the explicit
      -- `addConstInfo` below) semantic highlighting.
      -- Falls back to `SourceInfo.none` for chunks
      -- without source positions (e.g. macro-generated
      -- callsites).
      --
      -- Note: byte offsets are computed in the
      -- *decoded* chunk string, so a chunk containing
      -- escape sequences (e.g. `\<newline>` line
      -- continuations) yields positions that are off
      -- by the escape's width-difference. In practice
      -- `#refs` rarely sit after escapes within the
      -- same chunk, and the IDE tolerates being a few
      -- bytes off — typo errors from the elaborator
      -- still surface unchanged regardless.
      let info : SourceInfo := match chunkPos? with
        | some chunkPos =>
          let absStart : String.Pos.Raw :=
            ⟨chunkPos.byteIdx + 1 + startOff⟩
          let absEnd : String.Pos.Raw :=
            ⟨chunkPos.byteIdx + 1 + endOff⟩
          .original "".toRawSubstring absStart
            "".toRawSubstring absEnd
        | none => SourceInfo.none
      let ident : Ident := ⟨Syntax.ident info
        nameStr.toRawSubstring leanName []⟩
      -- Push an explicit `TermInfo` at the ident's
      -- substring range so `collectInfoBasedSemanticTokens`
      -- emits a highlight token there. The elaborator
      -- below also calls `addTermInfo` for the surrounding
      -- `@<ident>` node, but its range covers the wider
      -- expression rather than just the substring;
      -- pushing this leaf ensures the highlight lands on
      -- exactly the `#identifier` characters. Wrapped in
      -- `try ... catch` so a typo still surfaces from the
      -- elaboration of `@<ident>` below (with the same
      -- error message as before this rewrite) instead of
      -- being eaten here.
      try addConstInfo ident leanName
      catch _ => pure ()
      let strLit := Syntax.mkStrLit nameStr
      parts := parts.push
        (← `((Doc.refLinkOf @$ident:ident $strLit : Doc)))
    | .refByName name =>
      -- `#[name]` form: emit `Doc.refLinkByName "name"`.
      -- Unlike `.ref`, the name is not validated as a
      -- Lean identifier, so this admits labels whose
      -- characters fall outside the unbracketed `#name`
      -- form's accepted set or that need to abut
      -- surrounding prose without a terminator. No
      -- `addConstInfo` push: there is no resolved
      -- declaration to point semantic-token
      -- highlighting at.
      let lit := Syntax.mkStrLit name
      parts := parts.push
        (← `((Doc.refLinkByName $lit : Doc)))
    | .code s =>
      if s.isEmpty then continue
      let lit := Syntax.mkStrLit s
      parts := parts.push (← `((Doc.code $lit : Doc)))
    | .mathBlock mathSegs =>
      -- Build a `MathDoc.seq` of the math segments via
      -- the shared `mathSegsToTerm` helper (also used
      -- by the `mathdoc!` macro), then wrap in
      -- `Doc.math` so the math block fits into the
      -- enclosing `Doc.seq`.
      let mdTerm ← Doc.Interp.mathSegsToTerm mathSegs
      parts := parts.push
        (← `((Doc.math $mdTerm : Doc)))
    | .bold s =>
      -- `__X__` outside a math block: emit
      -- `Doc.bold (Doc.plain "X")`.
      let lit := Syntax.mkStrLit s
      parts := parts.push
        (← `((Doc.bold (Doc.plain $lit) : Doc)))
    | .italic s =>
      -- `_X_` outside a math block: emit
      -- `Doc.italic (Doc.plain "X")`.
      let lit := Syntax.mkStrLit s
      parts := parts.push
        (← `((Doc.italic (Doc.plain $lit) : Doc)))
  return parts

open Lean Elab Term in
@[term_elab docInterp]
def elabDocInterp : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(doc! $i:interpolatedStr) =>
    let chunks := i.raw.getArgs
    let mut parts : Array (TSyntax `term) := #[]
    for chunk in chunks do
      match chunk.isInterpolatedStrLit? with
      | some str =>
        if str.isEmpty then
          continue
        -- Position of the chunk's leading delimiter (the
        -- opening `"` for the first chunk, or `}` for chunks
        -- following an `{expr}` hole). The chunk's *content*
        -- begins one byte after that delimiter.
        let chunkPos? := chunk.getPos? (canonicalOnly := true)
        let segs := Doc.Interp.parseSegs str
        parts := parts ++
          (← Doc.Interp.chunkSegsToDocTerms chunkPos? segs)
      | none =>
        let term : Term := ⟨chunk⟩
        parts := parts.push (← `(($term : Doc)))
    let body ← `(Doc.seq [$parts,*])
    Lean.Elab.Term.elabTerm body expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

/-- Interpolated-string literal that desugars to a `MathDoc`
    value. The string contents are parsed with the same
    grammar used inside a `$...$` block of a `doc!` literal:
    Unicode math characters with a `MathSym` equivalent
    become `MathDoc.sym`, the rest become `MathDoc.raw`,
    `#identifier` becomes `MathDoc.text "<name>"` (a
    math-mode text rendering), and `__X__` / `_X_` produce
    bold / italic spans. Each `{expr}` interpolation hole
    becomes a `MathDoc`-typed term that is concatenated into
    the surrounding sequence.

    Used both standalone and as the canonical way to write
    enum-variant / struct / function display templates: the
    `defEnum` elaborator wraps a `mathdoc!` value in a
    function over the variant's arguments, so a free
    identifier `idx` inside the literal resolves to the
    bound `idx : MathDoc` parameter at rendering time. -/
syntax (name := mathdocInterp) "mathdoc! "
    interpolatedStr(term) : term

open Lean Elab Term in
@[term_elab mathdocInterp]
def elabMathDocInterp : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(mathdoc! $i:interpolatedStr) =>
    let chunks := i.raw.getArgs
    let mut parts : Array (TSyntax `term) := #[]
    for chunk in chunks do
      match chunk.isInterpolatedStrLit? with
      | some str =>
        if str.isEmpty then continue
        let segs := Doc.Interp.parseMathString str
        let mdTerm ← Doc.Interp.mathSegsToTerm segs
        parts := parts.push (← `(($mdTerm : MathDoc)))
      | none =>
        let term : Term := ⟨chunk⟩
        parts := parts.push (← `(($term : MathDoc)))
    let body ← `(MathDoc.seq [$parts,*])
    Lean.Elab.Term.elabTerm body expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax
