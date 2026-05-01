import Lean.Elab.Frontend
import Core.Doc
import Core.Export.Latex

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

/-- Walk `e` and return one `String` diagnostic per banned pattern
    found in any subtree, with `declName` (the enclosing decl) used
    to skip the unique sites where each pattern is permitted. -/
private partial def collectBanned (declName : Name) (e : Expr)
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
    -- one-liner that wraps this exact pattern. The exempt site is
    -- `MathDoc.text` itself, whose body is the wrapper.
    | .app (.const ``MathDoc.doc _)
        (.app (.const ``Doc.plain _) _) =>
      if declName == ``MathDoc.text then []
      else ["`MathDoc.doc (Doc.plain s)` should be `MathDoc.text s` \
             — the thin `MathDoc` wrapper that renders as `\\text{s}` \
             in LaTeX."]
    | _ => []
  let kids : List String := match e with
    | .app f a =>
      collectBanned declName f ++ collectBanned declName a
    | .lam _ t b _ | .forallE _ t b _ =>
      collectBanned declName t ++ collectBanned declName b
    | .letE _ t v b _ =>
      collectBanned declName t ++ collectBanned declName v
        ++ collectBanned declName b
    | .mdata _ e' | .proj _ _ e' => collectBanned declName e'
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
    for d in collectBanned n body do
      anyViolation.set true
      IO.eprintln s!"ERROR in {n}: {d}"
  if (← anyViolation.get) then
    IO.Process.exit 1
  else
    IO.println "-- Banned-pattern check passed."
    return 0
