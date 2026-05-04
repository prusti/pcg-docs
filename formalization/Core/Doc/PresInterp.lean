import Core.Doc.Interp
import Core.Dsl.Types.PresentationDef
import Lean

/-! # `presBody!` — markdown-like body builder for `Presentation.elems`

A template `Presentation` value's `elems` field is a `List PresElement`,
where each element is either free-form prose (`PresElement.doc`) or a
reference to a registered DSL definition by short name
(`PresElement.defRef`). Hand-writing the list constructor is noisy:
the prose-vs-defRef boundary forces the writer to think in terms of
list-element shape rather than running text.

The `presBody!` macro lets the same value be written as a single
markdown-like interpolated string:

```lean
elems := presBody! "
  # Places

  A focused look at the `Place` definition and its
  transitive dependencies.

  [[Place]]

  Definitions referenced by `Place` but not embedded directly
  here are rendered in the Appendix below."
```

## Body grammar

* `[[Name]]` — emits `PresElement.defRef "Name"`. `Name` must parse as
  a bare Lean identifier (`isIdentStart` head, `isIdentCont` rest, no
  dots). Any other shape (unclosed `[[`, empty `[[]]`, non-identifier
  body, dotted body) is left as literal characters in the surrounding
  prose, matching the unclosed-`$`/unclosed-backtick fallback in
  `Doc.Interp`.
* `# ` at the start of a line (after optional whitespace) — emits
  `PresElement.doc (Doc.section <line content>)`. The `# ` prefix
  is stripped; the rest of the line is parsed with the same inline
  grammar as `doc!`. `[[Name]]` is *not* recognised inside a heading.
* `--` at the start of a line (after optional whitespace) — line
  comment: the entire line is dropped from the output, including any
  `[[Name]]` it contains (so commented-out defRefs do *not* register
  for export). Comment lines are invisible to paragraph splitting:
  they neither introduce a paragraph break nor interrupt the
  soft-line-break joining of the prose lines around them. Mid-line
  `--` is *not* a comment marker — it stays as literal text.
* A blank line (run of `\n`s with optional whitespace between them)
  — paragraph break: finalises the in-progress prose chunk into a
  single `PresElement.doc` and starts a new one.
* A single newline inside a paragraph collapses to a space (markdown
  single-newline behaviour).
* `{expr}` — Doc-value interpolation hole, semantics identical to
  `doc!`'s `{expr}`. The spliced value is added to the in-progress
  paragraph; it does not by itself break the paragraph.
* All other inline syntax — backtick code, `$math$`, `_italic_`,
  `__bold__`, `#name` / `#[name]` cross-refs — is delegated unchanged
  to the existing `doc!` segment parser
  (`Doc.Interp.parseSegs`).

An empty prose chunk between two non-prose tokens (e.g. two adjacent
`[[Name]]`s on the same line) is dropped rather than emitted as an
empty `Doc.seq`. -/

namespace Doc.Interp

/-- A top-level token produced by the `presBody!` chunk parser, as
    seen by the elaborator's paragraph-accumulation pass. Inline
    grammar inside `prose` and `heading` runs is the same as in
    `doc!` and is carried as the existing `ChunkSeg` list. -/
private inductive PresChunkTok where
  /-- A run of inline prose to add to the current paragraph. -/
  | prose (segs : List ChunkSeg)
  /-- A blank-line break: end the current paragraph. -/
  | paraBreak
  /-- A `# ` heading line: end the current paragraph and emit a
      `Doc.section` element. -/
  | heading (segs : List ChunkSeg)
  /-- A `[[Name]]` definition reference: end the current paragraph
      and emit a `PresElement.defRef`. -/
  | defRefTok (name : String)
  deriving Inhabited

/-- Whitespace test for line-internal whitespace (space or tab).
    A `\n` is *not* whitespace here — newlines drive line
    transitions in the parser. -/
private def isHSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Strip a leading run of `isHSpace` characters from a char list. -/
private partial def dropHSpace : List Char → List Char
  | c :: rest => if isHSpace c then dropHSpace rest else c :: rest
  | [] => []

/-- Whether a line — represented as a char list with no embedded
    `\n` — is whitespace-only. -/
private def isBlankLine (cs : List Char) : Bool :=
  (dropHSpace cs).isEmpty

/-- Match `[[Name]]` at the head of `cs`. On success, returns the
    captured identifier and the remainder after `]]`. Returns
    `none` if `cs` does not start with `[[`, the closing `]]` is
    missing, the body is empty, or the body is not a bare
    identifier (mirrors `Doc.Interp.consumeRef`'s identifier
    rules: `isIdentStart` head, `isIdentCont` rest; no dots). -/
private def matchDefRef (cs : List Char) :
    Option (String × List Char) :=
  match cs with
  | '[' :: '[' :: rest =>
    let (name, after1) := consumeRef rest
    if String.isEmpty name then none
    else if (String.toList name).any (· == '.') then none
    else
      match after1 with
      | ']' :: ']' :: after => some (name, after)
      | _ => none
  | _ => none

/-- Split a single line's character list (no embedded `\n`) into
    `prose` / `defRefTok` tokens. Each `[[Name]]` breaks the line
    into a `prose` run before, a `defRefTok` token, and a `prose`
    run after; an unmatched or invalid `[[` is left as literal
    characters in the surrounding `prose` run. -/
private partial def tokenizeLine
    (acc : List Char) (chars : List Char) : List PresChunkTok :=
  match chars with
  | [] =>
    if List.isEmpty acc then []
    else
      let segs := parseSegs (String.ofList acc.reverse)
      [.prose segs]
  | '[' :: '[' :: rest =>
    match matchDefRef chars with
    | some (name, after) =>
      let lhs : List PresChunkTok :=
        if List.isEmpty acc then []
        else [.prose (parseSegs (String.ofList acc.reverse))]
      lhs ++ [.defRefTok name] ++ tokenizeLine [] after
    | none =>
      -- Treat the leading `[` as a literal char and re-enter
      -- the loop with the second `[` still at the head, so it
      -- can be reconsidered (e.g. the input was `[[[[Name]]`).
      tokenizeLine ('[' :: acc) ('[' :: rest)
  | c :: rest => tokenizeLine (c :: acc) rest

/-- Consume the body of a heading line (already stripped of its
    `# ` prefix and leading whitespace). The body is parsed with
    the same inline grammar as a `doc!` chunk; `[[Name]]` is *not*
    recognised inside a heading — a heading is a single
    `Doc.section` whose argument is a `Doc.seq`, so embedding a
    `defRef` inside would not type-check. -/
private def parseHeading (line : List Char) : List ChunkSeg :=
  parseSegs (String.ofList line)

/-- Walk a string chunk one line at a time, emitting `PresChunkTok`s
    that the elaborator weaves into paragraphs:

    * a whitespace-only line → `paraBreak` (idempotent — runs of
      blank lines collapse to a single paragraph break).
    * a line whose first non-whitespace characters are `# ` →
      `heading <inline-parsed body>`.
    * any other line → `tokenizeLine` (which produces `prose` and
      `defRefTok`s).

    Adjacent prose-bearing lines are joined by a single space, so
    soft line breaks (one `\n`) collapse to a space the way
    markdown handles them; the space is appended to the current
    line's prose run before that run is emitted, *unless* the
    previous emitted token was a `paraBreak` / `defRefTok` /
    `heading` (which already broke the paragraph). -/
private partial def tokenizeBody (s : String) :
    List PresChunkTok :=
  go (s.toList.splitOn '\n') false
where
  /-- `prevWasProseLine` tracks whether the most recent emitted
      tokens came from a prose-bearing line. When the next line is
      *also* prose, the previous run gets a trailing space appended
      (soft line break → space). -/
  go : List (List Char) → Bool → List PresChunkTok
  | [], _ => []
  | curLine :: rest, prevWasProseLine =>
    if isBlankLine curLine then
      .paraBreak :: go rest false
    else
      let stripped := dropHSpace curLine
      match stripped with
      | '-' :: '-' :: _ =>
        -- Line comment: drop the line entirely. `prevWasProseLine`
        -- is preserved so `prose / -- comment / prose` joins as a
        -- single paragraph, the same as a soft line break.
        go rest prevWasProseLine
      | '#' :: ' ' :: hdr =>
        .heading (parseHeading (dropHSpace hdr)) ::
          go rest false
      | _ =>
        let withLead :=
          if prevWasProseLine then ' ' :: curLine else curLine
        let toks := tokenizeLine [] withLead
        toks ++ go rest true

open Lean Elab Term in
/-- Build a `PresElement.doc (Doc.seq <parts>)` term from a list
    of accumulated paragraph parts, or `none` if the paragraph
    is empty (so empty paragraphs disappear instead of emitting
    `Doc.seq []`). -/
private def mkPresDocPara (parts : Array (TSyntax `term)) :
    TermElabM (Option (TSyntax `term)) := do
  if parts.isEmpty then return none
  let body ← `(Doc.seq [$parts,*])
  return some (← `((PresElement.doc $body : PresElement)))

open Lean Elab Term in
/-- Build a `PresElement.doc (Doc.section (Doc.seq <parts>))`
    term from a heading line's lowered Doc-segment terms. -/
private def mkPresHeading (parts : Array (TSyntax `term)) :
    TermElabM (TSyntax `term) := do
  let title ← `(Doc.seq [$parts,*])
  `((PresElement.doc (Doc.section $title) : PresElement))

open Lean Elab Term in
/-- Build a `PresElement.defRef <name>` term. -/
private def mkPresDefRef (name : String) :
    TermElabM (TSyntax `term) := do
  let lit := Syntax.mkStrLit name
  `((PresElement.defRef $lit : PresElement))

end Doc.Interp

/-- Interpolated-string literal that desugars to a
    `List PresElement` value, intended for `Presentation.elems`.

    See `Core.Doc.PresInterp`'s file-level docstring for the body
    grammar. -/
syntax (name := presBodyInterp) "presBody! "
    interpolatedStr(term) : term

open Lean Elab Term Doc.Interp in
@[term_elab presBodyInterp]
private def elabPresBodyInterp : Term.TermElab :=
    fun stx expectedType? => do
  match stx with
  | `(presBody! $i:interpolatedStr) =>
    let chunks := i.raw.getArgs
    let mut result : Array (TSyntax `term) := #[]
    let mut paraParts : Array (TSyntax `term) := #[]
    for chunk in chunks do
      match chunk.isInterpolatedStrLit? with
      | some str =>
        if str.isEmpty then continue
        let chunkPos? := chunk.getPos? (canonicalOnly := true)
        for tok in tokenizeBody str do
          match tok with
          | .prose segs =>
            paraParts := paraParts ++
              (← chunkSegsToDocTerms chunkPos? segs)
          | .paraBreak =>
            if let some t ← mkPresDocPara paraParts then
              result := result.push t
            paraParts := #[]
          | .heading segs =>
            if let some t ← mkPresDocPara paraParts then
              result := result.push t
            paraParts := #[]
            let lowered ← chunkSegsToDocTerms chunkPos? segs
            result := result.push (← mkPresHeading lowered)
          | .defRefTok name =>
            if let some t ← mkPresDocPara paraParts then
              result := result.push t
            paraParts := #[]
            result := result.push (← mkPresDefRef name)
      | none =>
        let term : Term := ⟨chunk⟩
        paraParts := paraParts.push (← `(($term : Doc)))
    if let some t ← mkPresDocPara paraParts then
      result := result.push t
    let body ← `([$result,*])
    Lean.Elab.Term.elabTerm body expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax
