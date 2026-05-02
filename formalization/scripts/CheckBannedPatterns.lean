import Lean.Elab.Frontend
import Core.Doc
import Core.Doc.Interp
import Core.Dsl.Lint
import Core.Export.Latex
import Core.Dsl.Types.EnumDef

/-! # Lean-AST banned-pattern check

Walks every user-written declaration in the requested packages and
flags constructor / call patterns that should never appear outside
their designated wrapper. Runs as `lake exe check_banned_patterns
Module1 Module2 ...` and replaces the older grep-based
`scripts/check_banned_patterns.sh`.

Compared to the shell version this:
- inspects post-elaboration `Expr` trees, so it sees `.plain s` /
  `.cmd "href"` regardless of dot-notation, namespace alias, or
  whether the call hides inside a `doc!` macro expansion;
- naturally handles multi-line and string-continuation cases the
  line-oriented grep can miss;
- emits a single Lean error per violation, citing the enclosing
  declaration name. -/

open Lean

/-- Whether `s` is a syntactically-clean (possibly dotted) Lean
    identifier — i.e. each `.`-separated component starts with a
    letter or underscore and contains only alphanumerics and
    underscores. Excludes strings with whitespace or punctuation
    (e.g. `"Value.fnPtr name"`, `"Some par"`) which the `#s`
    shorthand cannot represent. -/
private def isCleanIdent (s : String) : Bool :=
  let isStart (c : Char) := c.isAlpha || c == '_'
  let isCont (c : Char) := c.isAlphanum || c == '_'
  let parts := s.splitOn "."
  !parts.isEmpty && parts.all fun p =>
    !p.isEmpty && isStart p.front && p.all isCont

/-- Whether the string `s` is a (possibly dotted) DSL identifier
    registered with a hyperlink anchor — i.e. a name the `doc!`
    macro's `#s` shorthand would resolve to a real anchor:

    - undotted `s`: `s.fnDef` (a `defFn`), `s.propertyDef` (a
      `defProperty`), `s.inductivePropertyDef` (a
      `defInductiveProperty`), `s.enumDef` (a `defEnum`),
      `s.structDef` (a `defStruct`), or `s.aliasDef` (a
      `defAlias`) exists. All such definitions emit a
      `\hypertarget{fn:s}` anchor at their LaTeX rendering site
      (in addition to the kind-specific anchors `type:s` /
      `property:s`), which is the target `#s` resolves to;
    - dotted `s = X.Y`: `X.enumDef` (a `defEnum`) exists, whose
      constructors emit `\hypertarget{ctor:X.Y}` anchors. -/
private def isHyperlinkedIdent
    (env : Environment) (s : String) : Bool :=
  if !isCleanIdent s then false
  else
    match s.splitOn "." with
    | [] => false
    | [head] =>
      let base : Name := .mkSimple head
      let suffixes : List Name :=
        [`fnDef, `propertyDef, `inductivePropertyDef,
         `enumDef, `structDef, `aliasDef]
      suffixes.any fun suf =>
        (env.find? (base ++ suf)).isSome
    | head :: _ =>
      let base : Name := .mkSimple head
      (env.find? (base ++ `enumDef)).isSome

/-- Walk `e` and return one `String` diagnostic per banned pattern
    found in any subtree, with `declName` (the enclosing decl) used
    to skip the unique sites where each pattern is permitted. -/
private partial def collectBanned
    (env : Environment) (declName : Name) (e : Expr)
    : List String :=
  let here : List String := match e with
    -- `.cmd "href"` outside `Latex.externalLink`. `Latex.cmd`
    -- produces the text-mode `\href{...}{...}` form and
    -- `LatexMath.cmd` the math-mode variant; both should route
    -- through `Latex.externalLink`, which adds URL escaping and
    -- the blue-underline styling.
    | .app (.const ``Latex.cmd _) (.lit (.strVal "href"))
    | .app (.const ``LatexMath.cmd _) (.lit (.strVal "href")) =>
      if declName == ``Latex.externalLink then []
      else ["raw `.cmd \"href\"` — use `Latex.externalLink` instead, \
             which adds URL escaping and the blue-underline styling."]
    -- `MathDoc.doc (Doc.plain _)` should be `MathDoc.text _` — the
    -- one-liner that wraps this exact pattern. Exempt sites:
    -- - `MathDoc.text` itself (body is the wrapper);
    -- - `Doc.toDisplayParts` / `MathDoc.toDisplayParts` and their
    --   compiler-generated match helpers, which deliberately
    --   pattern-match on the canonical `.doc (.plain _)` shape to
    --   reclassify a `MathDoc.text` produced by `doc!`'s `#name`
    --   handler as a parameter slot. Pattern matches go through
    --   the constructor form regardless of which surface alias
    --   the user typed, so the ban — written for *construction*
    --   sites — has nothing useful to say here.
    | .app (.const ``MathDoc.doc _)
        (.app (.const ``Doc.plain _) _) =>
      let exempt : List Name :=
        [ ``MathDoc.text
        , ``Doc.toDisplayParts
        , ``MathDoc.toDisplayParts ]
      let isExempt := exempt.any fun n =>
        declName == n
        -- compiler-generated match helpers like
        -- `Doc.toDisplayParts._unsafe_rec` /
        -- `Doc.toDisplayParts.match_1` carry the parent decl
        -- as their name prefix.
        || n.isPrefixOf declName
      if isExempt then []
      else ["`MathDoc.doc (Doc.plain s)` should be `MathDoc.text s` \
             — the thin `MathDoc` wrapper that renders as `\\text{s}` \
             in LaTeX."]
    -- `Doc.code "<name>"` where `<name>` is a registered DSL
    -- identifier — both the explicit `.code "x"` form and the
    -- backtick shorthand `` `x` `` inside a `doc!` literal lower
    -- to this same `Doc.code` Expr. In either case `#x` should
    -- be used instead, since it produces the same monospace
    -- visible label *and* a hyperlink to the definition.
    | .app (.const ``Doc.code _) (.lit (.strVal s)) =>
      if isHyperlinkedIdent env s then
        [s!"`Doc.code \"{s}\"` (or backtick `\\`{s}\\`` inside a \
            `doc!` literal) names a registered DSL identifier — \
            replace with `#{s}` so the rendered output also \
            hyperlinks to the definition."]
      else []
    -- `MathDoc.raw "\\pi"` (and other single-symbol LaTeX
    -- commands listed in `rawMathSymbolToSym`) — `MathDoc.raw`
    -- bypasses every backend's symbol mapping and renders raw
    -- LaTeX, so a single Greek letter or operator dressed up as
    -- raw markup loses its meaning under Typst / HTML / plain
    -- text. The structured `MathDoc.sym` constructor renders
    -- correctly for every backend; for sources where the symbol
    -- appears inside a `doc!` literal, the matching Unicode
    -- character (`π`, `μ`, `α`, `θ`, `ϕ`, `φ`) is also accepted
    -- and translated by the interpolator into the same
    -- `MathDoc.sym` form. The check trims surrounding whitespace
    -- so `.raw "\\pi"` and `.raw "\\pi "` are both flagged.
    | .app (.const ``MathDoc.raw _) (.lit (.strVal s)) =>
      match DslLint.rawMathSymbolToSym s with
      | some symName =>
        [s!"`MathDoc.raw \"{s}\"` renders a single math symbol via \
            raw LaTeX — use `MathDoc.sym .{symName}` (or the \
            anonymous-constructor form `.sym .{symName}`) instead. \
            Inside a `doc!` literal, write the matching Unicode \
            character (e.g. `π`, `ϕ`, `φ`, `μ`, `α`, `θ`) and the \
            interpolator emits the structured form for you."]
      | none => []
    -- `Doc.math (MathDoc.sym _)` (or its `Doc.m` reducible
    -- shorthand) — a hand-written math symbol splice such as
    -- `{Doc.m (.sym .emptySet)}` inside a `doc!` literal.
    -- Authors should write the matching Unicode character
    -- (`∅`, `∪`, `∩`, …) directly in the prose: the `doc!`
    -- interpolator wraps such characters in
    -- `Doc.math (MathDoc.seq [MathDoc.sym …])` automatically,
    -- which keeps the source readable and (because of the
    -- `MathDoc.seq` envelope) is structurally distinct from the
    -- pattern we're banning here. `defEnum` variant displays
    -- and `MathDoc.seq`-internal uses bypass this since they
    -- never wrap a bare `Doc.math` (or `Doc.m`) around a bare
    -- `MathDoc.sym`. The pattern matches both `Doc.math` and
    -- `Doc.m`: the latter is a reducible abbreviation but Lean
    -- still records the surface name in elaborated `Expr`s
    -- before reduction.
    | .app (.const head _)
        (.app (.const symHead _) (.const symName _)) =>
      if (head == ``Doc.math || head == ``Doc.m)
          && symHead == ``MathDoc.sym then
        let unqual := symName.componentsRev.head?.getD .anonymous
        let symStr := match unqual with
          | .str _ s => s | _ => toString unqual
        [s!"`Doc.math (MathDoc.sym .{symStr})` (or the equivalent \
            shorthand `Doc.m (.sym .{symStr})`) inside a `doc!` \
            literal — write the matching Unicode character \
            directly (e.g. `∅`, `∪`, `∩`) and let the \
            interpolator wrap it in a one-segment math block."]
      else []
    | _ => []
  let kids : List String := match e with
    | .app f a =>
      collectBanned env declName f ++ collectBanned env declName a
    | .lam _ t b _ | .forallE _ t b _ =>
      collectBanned env declName t ++ collectBanned env declName b
    | .letE _ t v b _ =>
      collectBanned env declName t ++ collectBanned env declName v
        ++ collectBanned env declName b
    | .mdata _ e' | .proj _ _ e' => collectBanned env declName e'
    | _ => []
  here ++ kids

/-- Whether the declaration `n` was declared in a module whose
    package root (`Name.getRoot`) matches that of one of the
    requested `roots`. Decl names themselves don't carry their
    defining module, so we look it up via
    `env.getModuleIdxFor?` and consult `env.header.moduleNames`.
    Restricting to user-package roots keeps us from walking the
    stdlib / Batteries decls that `importModules` transitively
    brings into scope. -/
private def isFromUserPackage
    (env : Environment) (roots : List Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    match env.header.moduleNames[idx]? with
    | none => false
    | some modName =>
      roots.any fun r => modName.getRoot == r.getRoot

unsafe def main (args : List String) : IO UInt32 := do
  let modules := args.map String.toName
  if modules.isEmpty then
    IO.eprintln "Usage: check_banned_patterns Module1 Module2 ..."
    return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := modules.map fun m => ({ module := m } : Import)
  let env ← importModules imports.toArray {}
    (trustLevel := 1024) (loadExts := true)
  let anyViolation ← IO.mkRef false
  env.constants.forM fun n ci => do
    if n.hasMacroScopes then return
    if !isFromUserPackage env modules n then return
    let some body := ci.value? | return
    for d in collectBanned env n body do
      anyViolation.set true
      IO.eprintln s!"ERROR in {n}: {d}"
  if (← anyViolation.get) then
    IO.Process.exit 1
  else
    IO.println "-- Banned-pattern check passed."
    return 0
