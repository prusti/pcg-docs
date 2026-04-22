import Core.Doc
import Lean

/-!
# `latex!` — parse a LaTeX snippet into a `MathDoc` at compile time.

This is a deliberately small parser: it covers the constructs that
appear in inline math snippets in the PCG presentation (variables
and subscripts like `t_D` / `t_{prev}`), nothing more. New
constructs should be added on demand rather than by trying to
support full LaTeX.

## Supported grammar

```
math   ::= factor*                 -- whitespace-separated sequence
factor ::= atom (`_` group)?       -- optional subscript
group  ::= varchar | `{` math `}`  -- single char or braced group
atom   ::= varchar+                -- run of letters / digits / `'`
```

Whitespace inside a snippet is treated as a token separator and
discarded from the resulting `MathDoc`. Anything else (`\foo`,
`^`, `+`, `(`, `)`, …) is rejected with a parse error.

## Examples

```
latex! "t_D"      -- MathDoc.sub (.raw "t") (.raw "D")
latex! "t_{prev}" -- MathDoc.sub (.raw "t") (.raw "prev")
latex! "x y z"    -- MathDoc.seq [.raw "x", .raw "y", .raw "z"]
```
-/

namespace LatexParse

/-- Whether `c` is a character that may appear in an atom. We treat
    letters, digits, and `'` (used for primed identifiers like `x'`)
    as part of the same token. -/
private def isAtomChar (c : Char) : Bool :=
  c.isAlphanum || c == '\''

/-- Whether `c` is whitespace that we skip silently. -/
private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n'

/-- Result of consuming a token: the produced value plus the
    remaining input. -/
private structure Step (α : Type) where
  value : α
  rest : List Char
  deriving Inhabited

private def skipWs : List Char → List Char
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | [] => []

private partial def takeAtomGo
    (acc : List Char) : List Char → List Char × List Char
  | c :: rest =>
    if isAtomChar c then takeAtomGo (c :: acc) rest
    else (acc.reverse, c :: rest)
  | [] => (acc.reverse, [])

/-- Consume a maximal run of `isAtomChar` characters. Fails if the
    first character is not an atom character. -/
private def takeAtom (cs : List Char) : Except String (Step String) :=
  match cs with
  | c :: _ =>
    if isAtomChar c then
      let (chars, rest) := takeAtomGo [] cs
      .ok { value := String.ofList chars, rest }
    else .error s!"expected atom character, got '{c}'"
  | [] => .error "expected atom character, got end of input"

mutual
  /-- Parse a (possibly empty) sequence of factors. Stops at end of
      input or at a closing `}`. -/
  private partial def parseSeq
      (cs : List Char) : Except String (Step MathDoc) :=
    parseSeqGo [] (skipWs cs)

  /-- Tail-recursive worker for `parseSeq`. -/
  private partial def parseSeqGo
      (acc : List MathDoc) (rest : List Char)
      : Except String (Step MathDoc) :=
    match rest with
    | [] => finish acc rest
    | '}' :: _ => finish acc rest
    | _ =>
      match parseFactor rest with
      | .error e => .error e
      | .ok step =>
        parseSeqGo (acc ++ [step.value]) (skipWs step.rest)
  where
    finish (acc : List MathDoc) (rest : List Char)
        : Except String (Step MathDoc) :=
      let value := match acc with
        | [] => MathDoc.raw ""
        | [m] => m
        | ms => MathDoc.seq ms
      .ok { value, rest }

  /-- Parse a single `atom (_ group)?`. -/
  private partial def parseFactor
      (cs : List Char) : Except String (Step MathDoc) := do
    let baseStep ← takeAtom cs
    let base := MathDoc.raw baseStep.value
    match baseStep.rest with
    | '_' :: more =>
      let subStep ← parseGroup more
      .ok { value := MathDoc.sub base subStep.value
          , rest := subStep.rest }
    | _ => .ok { value := base, rest := baseStep.rest }

  /-- Parse a subscript argument: either a single atom character or
      a brace-delimited sub-expression. -/
  private partial def parseGroup
      (cs : List Char) : Except String (Step MathDoc) := do
    match cs with
    | '{' :: more =>
      let inner ← parseSeq more
      match inner.rest with
      | '}' :: rest => .ok { value := inner.value, rest }
      | _ => .error "unterminated brace group after underscore"
    | c :: _ =>
      if isAtomChar c then
        do let s ← takeAtom cs
           .ok { value := MathDoc.raw s.value, rest := s.rest }
      else
        .error s!"expected atom or open-brace after _, got '{c}'"
    | [] => .error "unexpected end of input after underscore"
end

/-- Parse a LaTeX snippet to a `MathDoc`. Whitespace inside the
    snippet is dropped; an empty snippet yields `MathDoc.raw ""`. -/
def parse (src : String) : Except String MathDoc := do
  let step ← parseSeq src.toList
  match step.rest with
  | [] => .ok step.value
  | c :: _ => .error s!"unexpected character '{c}'"

end LatexParse

namespace MathDoc

open Lean

/-- Quote a `MathDoc` value as a Lean term that, when elaborated,
    rebuilds the same value. Only the constructors actually emitted
    by `LatexParse.parse` need to be supported here. -/
partial def toTerm : MathDoc → MacroM (TSyntax `term)
  | .raw s => `(MathDoc.raw $(quote s))
  | .sub b s => do
    `(MathDoc.sub $(← b.toTerm) $(← s.toTerm))
  | .seq ms => do
    let elems ← ms.mapM toTerm
    `(MathDoc.seq [$(elems.toArray),*])
  | _ => Macro.throwError
      "MathDoc.toTerm: unsupported constructor (LatexParse \
       only emits .raw / .sub / .seq)"

end MathDoc

/-- Compile-time LaTeX-to-`MathDoc` parser. Accepts the small
    grammar described in `Core.Dsl.LatexParse` (atoms and
    subscripts). Use `latex!` for math fragments embedded in Lean
    source code:

    ```
    example : MathDoc := latex! "t_D"
    example : MathDoc := latex! "t_{prev}"
    ```

    Wrap the result in `Doc.math` to embed it in a `Doc`. -/
syntax (name := latexMacro) "latex!" str : term

open Lean Elab in
@[macro latexMacro]
def latexMacroImpl : Macro := fun stx =>
  match stx with
  | `(latex! $s:str) =>
    match LatexParse.parse s.getString with
    | .ok md => md.toTerm
    | .error e => Macro.throwErrorAt s
        s!"latex! parse error: {e}"
  | _ => Macro.throwUnsupported
