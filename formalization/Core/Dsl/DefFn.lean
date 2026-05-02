import Core.Doc.Interp
import Core.Registry
import Core.Export.Lean
import Core.Dsl.DefEnum
import Core.Dsl.IdentRefs
import Core.Dsl.Lint
import Runtime
import Lean

open Core.Dsl.IdentRefs

open Lean in

declare_syntax_cat fnParam
syntax "(" ident term ":" term ")" : fnParam

declare_syntax_cat fnPat
declare_syntax_cat fnPatAtom
syntax "_" : fnPatAtom
syntax ident : fnPatAtom
syntax num : fnPatAtom
syntax "[" "]" : fnPatAtom
syntax "[" fnPat,+ "]" : fnPatAtom
syntax "⟨" fnPat,+ "⟩" : fnPatAtom
syntax "(" fnPat ")" : fnPatAtom
syntax fnPatAtom : fnPat
syntax "_" : fnPat
syntax ident : fnPat
syntax "." ident fnPatAtom* : fnPat
syntax ident "." ident fnPatAtom* : fnPat
syntax num : fnPat
syntax "⟨" fnPat,+ "⟩" : fnPat
syntax "(" fnPat ")" : fnPat
syntax "[" "]" : fnPat
syntax "[" fnPat,+ "]" : fnPat
syntax fnPat " :: " fnPat : fnPat

declare_syntax_cat fnExpr
-- Atom-precedence forms (`:max`) qualify as arguments
-- to the Haskell-style juxtaposition application parser
-- `fnExprApp` registered below.
syntax:max "[" "]" : fnExpr
syntax:max "[" fnExpr,+ "]" : fnExpr
syntax:max num : fnExpr
syntax:max ident : fnExpr
syntax:max "(" fnExpr ")" : fnExpr
-- Method call: `expr·name`. Default precedence so `·name`
-- can extend a leadPrec juxtaposition like `(f a b)·field`
-- without protective parens.
syntax fnExpr "·" ident : fnExpr
syntax fnExpr "·flatMap" "fun" fnPat "=>" fnExpr
    : fnExpr
syntax fnExpr "·map" "fun" fnPat "=>" fnExpr
    : fnExpr
syntax fnExpr "·map" ident : fnExpr
syntax fnExpr " :: " fnExpr : fnExpr
syntax fnExpr " ++ " fnExpr : fnExpr
syntax "Some" fnExpr : fnExpr
syntax "None" : fnExpr
-- Anonymous tuple/struct literal — `:max` so it qualifies
-- as a juxtaposition argument.
syntax:max "⟨" fnExpr,+ "⟩" : fnExpr
-- Named struct constructor: Name⟨a, b⟩ — also `:max`.
syntax:max ident "⟨" fnExpr,+ "⟩" : fnExpr
-- Field access chain: `expr↦name`. `:max` because the
-- `↦name` suffix is syntactically atomic and the whole form
-- can be passed as a juxtaposition argument without parens
-- (`f bb↦terminator` instead of `f (bb↦terminator)`).
syntax:max fnExpr "↦" ident : fnExpr
-- Functional struct update: `expr[field => newValue]`.
-- `:max` — the closing `]` makes the whole form atomic.
-- Wrapped in `atomic` so a `(args [])`-style expression
-- (where the `[]` opens a list literal in the next argument)
-- doesn't commit to this rule and then fail at the missing
-- `=>`.
syntax:max fnExpr (atomic("[" ident " => ") fnExpr "]") : fnExpr
-- Fallible indexing: `expr !! expr` (for `list[idx]?`).
-- The RHS is `:max` so the operator binds tightly:
-- `xs !! i + 1` parses as `(xs !! i) + 1` (and you'd write
-- `xs !! (i + 1)` for the other grouping). The whole form
-- is `:max` so it's an atomic juxtaposition argument.
syntax:max fnExpr "!!" fnExpr:max : fnExpr
-- Infallible indexing: `expr ! expr` (for `list[idx]`).
syntax:max fnExpr "!" fnExpr:max : fnExpr
-- Zero-argument call: `fn‹›`. Kept as a distinct form
-- (rather than collapsing to the bare `fn` variable)
-- because the AST distinction matters for Rust: `.call _ []`
-- exports as `fn()` while `.var "fn"` exports as `fn` (a
-- function pointer). The Lean / LaTeX exporters render both
-- as `fn`, so the rendered output is unchanged either way.
syntax:max ident "‹" "›" : fnExpr
-- Dot-prefixed nullary variant: .leaf — also `:max` so it
-- qualifies as a juxtaposition argument.
syntax:max "." ident : fnExpr
-- FoldlM: expr "·foldlM" ident expr
syntax fnExpr "·foldlM" ident fnExpr : fnExpr
-- Less-than: expr < expr
syntax:50 fnExpr:51 " < " fnExpr:51 : fnExpr
-- Chained less-than: expr < expr < expr
syntax:50 fnExpr:51 " < " fnExpr:51 " < " fnExpr:51
    : fnExpr
-- Less-than-or-equal: expr ≤ expr.
-- All inequality rules are non-associative (own prec 50,
-- arg prec 51) so that Lean unambiguously picks the
-- longest matching chain rule.
syntax:50 fnExpr:51 " ≤ " fnExpr:51 : fnExpr
-- Chained ≤ (3 elements): expr ≤ expr ≤ expr
syntax:50 fnExpr:51 " ≤ " fnExpr:51 " ≤ " fnExpr:51
    : fnExpr
-- Chained ≤ (4 elements): expr ≤ expr ≤ expr ≤ expr
syntax:50 fnExpr:51 " ≤ " fnExpr:51 " ≤ " fnExpr:51
    " ≤ " fnExpr:51 : fnExpr
-- Mixed chain: expr < expr ≤ expr
syntax:50 fnExpr:51 " < " fnExpr:51 " ≤ " fnExpr:51
    : fnExpr
-- Arithmetic: bind tighter than `≤` so that
-- `a + b ≤ c` parses as `(a + b) ≤ c` and chains like
-- `a ≤ b + c ≤ d` work as expected.
syntax:65 fnExpr:65 " + " fnExpr:66 : fnExpr
syntax:65 fnExpr:65 " - " fnExpr:66 : fnExpr
syntax:70 fnExpr:70 " * " fnExpr:71 : fnExpr
syntax:70 fnExpr:70 " / " fnExpr:71 : fnExpr
-- Empty set: ∅
syntax "∅" : fnExpr
-- Set singleton: ⦃ expr ���
syntax "⦃" fnExpr "⦄" : fnExpr
-- Set union: expr ∪ expr
syntax fnExpr " ∪ " fnExpr : fnExpr
-- Set flat-map: expr ·setFlatMap fun pat => expr.
-- The pattern may destructure tuples (⟨a, b, c⟩) so that
-- recursive callers can project parts without a nested match.
syntax fnExpr "·setFlatMap" "fun" fnPat "=>" fnExpr
    : fnExpr
-- Universal quantifier over a set: expr ·forAll fun ident =>
-- expr. Uses ident only (not fnPat) because the generated
-- Lean form `∀ param ∈ set, body` does not accept anonymous
-- destructuring in the binder.
syntax fnExpr "·forAll" "fun" ident "=>" fnExpr
    : fnExpr
-- Set/list membership: expr ∈ expr.
-- Prec 50 — same level as the comparison ops `<` / `≤` so it
-- is rejected when those rules look for a tightly-bound RHS,
-- instead of being absorbed greedily.
syntax:50 fnExpr:51 " ∈ " fnExpr:51 : fnExpr
-- Logical conjunction: expr ∧ expr.
-- Prec 35 (matching Lean's standard) so `a < b ∧ c < d` parses
-- as `(a < b) ∧ (c < d)` rather than `a < (b ∧ c < d)`.
syntax:35 fnExpr:36 " ∧ " fnExpr:35 : fnExpr
-- Conjunction with a soft line break before the `∧`. Renders
-- as `a ⏎ ∧ b` (the operator starts the next line) rather
-- than `a ∧ ⏎ b` (the prefix form `a ∧ ‹break› b`).
-- The atom is intentionally `‹break›∧` (no space) to keep the
-- token disjoint from the leading `‹break›` prefix marker —
-- without that, the parser cannot decide between the two when
-- chaining (`a ‹break› ∧ b ‹break› → c`) and bails on the
-- `‹break›` after `b`.
syntax:35 fnExpr:36 " ‹break›∧ " fnExpr:35 : fnExpr
-- Logical disjunction: expr ∨ expr. Prec 30, looser than `∧`.
syntax:30 fnExpr:31 " ∨ " fnExpr:30 : fnExpr
-- Implication: expr → expr. Prec 25, right-associative —
-- looser than `∨` so `a ∨ b → c ∨ d` parses as
-- `(a ∨ b) → (c ∨ d)`.
syntax:25 fnExpr:26 " → " fnExpr:25 : fnExpr
-- Implication with a soft line break before the `→`.
-- Same right-associativity / precedence as the bare `→`;
-- emits the break so the operator starts the next line.
-- Spelled `‹break›→` for the same disambiguation reason as
-- `‹break›∧` above.
syntax:25 fnExpr:26 " ‹break›→ " fnExpr:25 : fnExpr
-- Universal-quantifier binder group:
--   * `x` — a single untyped variable.
--   * `x y z ∈ T` — one or more variables sharing a type.
declare_syntax_cat fnForallGroup
syntax (name := fnForallGroupUntyped) ident : fnForallGroup
syntax (name := fnForallGroupTyped) ident+ " ∈ " ident
  : fnForallGroup

-- Universal quantifier with one or more comma-separated
-- binder groups followed by `.` and the body:
--   `∀∀ pr ∈ Program, ar ∈ AnalysisResults, p p' ∈ Place . body`
-- LaTeX renders as `∀ pr ∈ Program, ar ∈ AnalysisResults,
-- p p' ∈ Place, body`; Lean renders as
-- `∀ (pr : Program) (ar : AnalysisResults) (p p' : Place), body`.
syntax "∀∀" sepBy1(fnForallGroup, ", ") " . " fnExpr : fnExpr
-- Proof placeholder
syntax "sorry" : fnExpr
-- Raw Lean proof term (invisible in Rust/LaTeX). The body
-- between the brackets is a real Lean `term`, not a string —
-- so a typo or unresolved name surfaces as a Lean elaboration
-- error rather than slipping through as opaque text.
syntax:max "proof[" term "]" : fnExpr
-- Presentation-only formatting hint: a soft line break
-- inserted before the next expression in the LaTeX
-- rendering. The Lean and Rust exports pass the wrapped
-- expression through unchanged. Authored as a prefix marker:
--     a → ‹break› b → ‹break› c
-- The wrapped sub-expression is parsed at prec 51 so binary
-- operators (`→` at 25, `∧` at 35, …) stop at the marker and
-- the chain right-associates as `a → ((‹break› b) → (‹break› c))`.
syntax "‹break›" fnExpr:51 : fnExpr

-- Haskell-style function-application juxtaposition. Mirrors
-- Lean's own `Term.app := trailing_parser:leadPrec:maxPrec
-- many1 argument` — declared via Lean parser combinators
-- rather than the `syntax` macro because `syntax` can't
-- express the trailing-parser shape needed for a
-- left-recursive juxtaposition. The result lives at
-- `:leadPrec` (lower than `:maxPrec`) so when this parser
-- recursively asks for an argument at `:max`, the trailing
-- parser doesn't fire again — that's what gives
-- left-associative parsing (`f n 0` → `(f n) 0` rather than
-- `f (n 0)`). Each argument is parsed at `:max` (atomic —
-- bare ident, num, paren-wrapped, list/tuple/struct literal,
-- …); compound arguments (top-level `↦`, `+`, `::`,
-- `m[fld => v]`, …) need protective parens. Whitespace
-- between head and arg isn't required: the DSL never uses
-- the `f(x)` (no-space) shape — the prior `fnPrecond`
-- property-call form `Name(args)` was migrated to the same
-- bracketless `Name args` juxtaposition this parser handles
-- — so `f(x)` and `f (x)` both parse as application.
open Lean Parser in
@[fnExpr_parser] def fnExprApp :=
  trailing_parser:leadPrec:maxPrec
    many1 (categoryParser `fnExpr maxPrec)

declare_syntax_cat fnArm
syntax "| " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat " => " fnExpr
    : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat "; " fnPat
    " => " fnExpr : fnArm

-- Match expression: match expr with | pat => expr end
syntax "match " fnExpr " with" fnArm+ " end" : fnExpr
-- Match with scrutinee equation bound as a hypothesis:
-- `match h : expr with | pat => expr end`. Each arm's RHS
-- has access to `h` recording the equality between the
-- scrutinee and the matched pattern. The Lean export emits
-- `match h : scrut with`; the LaTeX/Rust exports drop the
-- binder.
syntax "match " ident " : " fnExpr " with" fnArm+ " end" : fnExpr

-- If-then-else expression: if cond then t else e
syntax "if " fnExpr " then " fnExpr " else " fnExpr : fnExpr
-- Inequality: expr ≠ expr.
-- Prec 50 to match the comparison ops `<` / `≤` / `∈`, so it
-- is rejected when looser binops (`∧`, `∨`, `→`) try to absorb
-- it as a tightly-bound argument.
syntax:50 fnExpr:51 " ≠ " fnExpr:51 : fnExpr
-- Decidable / `BEq` equality: expr == expr (renders to Bool).
-- Prec 50, same rationale as `≠`.
syntax:50 fnExpr:51 " == " fnExpr:51 : fnExpr
-- Propositional equality: expr = expr (renders to Lean's `=`,
-- i.e. `Eq`). Distinct from `==` so that `Prop`-level
-- positions (property bodies, inductive-property premises)
-- can express equality without coercing through `Bool`.
-- Prec 50, same rationale as `≠` / `==`.
syntax:50 fnExpr:51 " = " fnExpr:51 : fnExpr
-- List existential: expr ·any fun pat => expr
syntax fnExpr "·any" "fun" fnPat "=>" fnExpr : fnExpr

-- Let-in expression: let pat := e1 ; e2. The binder accepts
-- any `fnPat` so that tuple destructuring (`let ⟨a, b⟩ := …`)
-- works; a bare identifier reduces to the single-binder form.
syntax "let " fnPat " := " fnExpr " ; " fnExpr : fnExpr
-- Option bind: let pat ← e1 ; e2 (pattern allows
-- destructuring such as `let ⟨a, b⟩ ← …`).
syntax "let " fnPat " ← " fnExpr " ; " fnExpr : fnExpr

declare_syntax_cat fnStmt
syntax "let " fnPat " := " fnExpr : fnStmt
syntax "let " fnPat " ← " fnExpr : fnStmt

declare_syntax_cat fnPrecond
-- The `fnPrecond` shapes: any DSL expression that evaluates
-- to `Prop` or `Bool`. Allows preconditions like
-- `requires xs·length = ys·length` (an arbitrary expression)
-- and the bracketless property-call form
-- `requires Name arg₁ arg₂ …` (a juxtaposition the
-- `parsePrecond` matcher recognises and lowers to a `.named`
-- precondition so the proof binder stays `h_<Name>`). The
-- legacy parenthesised `Name(arg₁, arg₂)` form was dropped:
-- every existing call site already uses Haskell-style
-- application both in `requires` / `ensures` clauses and in
-- the surrounding function bodies.
syntax fnExpr : fnPrecond
-- General-expression form with a `using [lemma, …]` clause:
-- extra simp lemma names spliced into the auto-discharge
-- tactic the Lean backend emits at recursive call sites.
syntax fnExpr "using" "[" ident,+ "]" : fnPrecond

/-- Pattern-matching function.

    An optional `displayed (part, …)` clause may follow the
    parameter list (before `requires` / `:`). It controls how
    the function signature is rendered in the LaTeX
    presentation, mirroring the display templates of `defEnum`
    variants. Argument references inside the template (`#name`)
    auto-look-up the parameter type's `symbolDoc`; an explicit
    symbol may be supplied as `#name (symbolDoc)`. Literal
    parts are `MathDoc` terms (e.g. `.sym .lbracket`,
    `.sym .mapsto`, raw strings via the `String → Doc`
    coercion). When omitted, the LaTeX caption falls back to
    the default `name(p₁, p₂, …)` rendering.

    Example:
    ```
    defFn setOwnedLocalAt (.plain "setOwnedLocalAt")
      (.plain "Replace the owned local at a given index.")
      (os "The owned state." : OwnedState)
      (idx "The local index." : Nat)
      (newOl "The replacement local." : OwnedLocal)
      displayed (#os, .sym .lbracket, #idx,
                 .sym .mapsto, #newOl, .sym .rbracket)
      : OwnedState := …
    ```
    renders the algorithm caption as `os[idx ↦ ol] → OwnedState`
    instead of `setOwnedLocalAt(os, idx, newOl) → OwnedState`. -/
syntax "defFn " ("implicit ")? ("@[" ident,+ "]")?
    ident "(" term ")" "(" term ")"
    fnParam* ("displayed " "(" displayPart,+ ")")?
    ("requires " fnPrecond,+)?
    ("ensures " fnPrecond,+)?
    ":" term " where" fnArm* : command

/-- Direct expression function (no pattern match). See the
    pattern-matching form for the optional `displayed` clause.
    The optional `implicit` modifier hides the function from
    the LaTeX presentation entirely: the algorithm block is
    suppressed and call sites render as their argument alone.
    `implicit` is only accepted when the function takes
    exactly one explicit parameter.

    An optional `@[attr₁, attr₂, …]` clause between `defFn`
    (or `defFn implicit`) and the function name attaches those
    attributes to the generated Lean definition — typically
    `@[simp]` to make the function unfold inside `simp`
    rewrites. The DSL just prepends `@[attr₁, attr₂, …]`
    verbatim to the rendered `def` line; it does not validate
    or restrict the attribute names, so any attribute Lean
    accepts on a `def` is fair game. -/
syntax "defFn " ("implicit ")? ("@[" ident,+ "]")?
    ident "(" term ")" "(" term ")"
    fnParam* ("displayed " "(" displayPart,+ ")")?
    ("requires " fnPrecond,+)?
    ("ensures " fnPrecond,+)?
    ":" term " :=" fnExpr : command

-- ══════════════════════════════════════════════
-- Parsing helpers
-- ══════════════════════════════════════════════

mutual
partial def parsePatAtom
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPatAtom| _) => pure .wild
  | `(fnPatAtom| $n:ident) => do
    recordLocalBinder n n.getId
    pure (.var (toString n.getId))
  | `(fnPatAtom| $n:num) => pure (.natLit n.getNat)
  | `(fnPatAtom| [ ]) => pure .nil
  | `(fnPatAtom| [ $ps:fnPat,* ]) => do
    let parsed ← ps.getElems.mapM parsePat
    pure (parsed.foldr BodyPat.cons .nil)
  | `(fnPatAtom| ⟨ $args:fnPat,* ⟩) => do
    let a ← args.getElems.mapM parsePat
    pure (.ctor "⟨⟩" a.toList)
  | `(fnPatAtom| ( $p:fnPat )) => parsePat p
  | _ => Lean.Elab.throwUnsupportedSyntax

partial def parsePat
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPat| $a:fnPatAtom) => parsePatAtom a
  | `(fnPat| _) => pure .wild
  | `(fnPat| $n:ident) => do
    recordLocalBinder n n.getId
    pure (.var (toString n.getId))
  | `(fnPat| .$n:ident $args:fnPatAtom*) => do
    let a ← args.mapM parsePatAtom
    pure (.ctor (toString n.getId) a.toList)
  | `(fnPat| $en:ident . $n:ident $args:fnPatAtom*) => do
    let a ← args.mapM parsePatAtom
    pure (.ctor s!"{en.getId}.{n.getId}" a.toList)
  | `(fnPat| ⟨$args:fnPat,*⟩) => do
    let a ← args.getElems.mapM parsePat
    pure (.ctor "⟨⟩" a.toList)
  | `(fnPat| ($p:fnPat)) => parsePat p
  | `(fnPat| $n:num) => pure (.natLit n.getNat)
  | `(fnPat| [ ]) => pure .nil
  | `(fnPat| [ $ps:fnPat,* ]) => do
    let parsed ← ps.getElems.mapM parsePat
    pure (parsed.foldr BodyPat.cons .nil)
  | `(fnPat| $h:fnPat :: $t:fnPat) =>
    pure (.cons (← parsePat h) (← parsePat t))
  | _ => Lean.Elab.throwUnsupportedSyntax
end

partial def parseExpr
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM DslExpr := do
  -- Haskell-style application `head arg₁ arg₂ …` — the
  -- trailing parser `fnExprApp` produces a node of kind
  -- `fnExprApp` whose first child is the LHS fnExpr and
  -- whose second child is the `many1` array of arguments.
  -- A `head` that's already a `.call` (e.g. produced by a
  -- nested left-associative parse) gets its args list
  -- extended; everything else becomes a fresh `.call`.
  if stx.isOfKind ``fnExprApp then
    let head ← parseExpr stx[0]
    let args ← stx[1].getArgs.mapM parseExpr
    match head with
    | .call f existing => return .call f (existing ++ args.toList)
    | _ => return .call head args.toList
  match stx with
  | `(fnExpr| [ ]) => pure .emptyList
  | `(fnExpr| [ $es:fnExpr,* ]) => do
    let elems ← es.getElems.mapM parseExpr
    pure (elems.foldr DslExpr.cons .emptyList)
  | `(fnExpr| $n:num) =>
    pure (.natLit n.getNat)
  | `(fnExpr| $n:ident) =>
    let name := toString n.getId
    match name with
    | "true" => pure .true_
    | "false" => pure .false_
    | _ =>
      recordIdentRef n n.getId
      pure (.var name)
  | `(fnExpr| ($e:fnExpr)) => parseExpr e
  | `(fnExpr| $r:fnExpr · $m:ident) => do
    let recv ← parseExpr r
    -- Record a goto-def target for the method token by
    -- looking up `m` in the global fn registry, augmented
    -- with constants newly added to the env in this same
    -- module (where the registry's `initialize` block hasn't
    -- run yet). The synthesised Lean rendering `recv.m`
    -- carries no user-source position for `m`, so without
    -- this leaf gotoDef on `m` (e.g. `bodyPlaces` in
    -- `body·bodyPlaces`) lands nowhere.
    let env ← Lean.MonadEnv.getEnv
    let qualifieds ← resolveFnByShortName env (toString m.getId)
    for qualified in qualifieds do
      recordIdentRef m qualified
    pure (.dot recv (toString m.getId))
  | `(fnExpr| $r:fnExpr ·flatMap fun $p:fnPat =>
        $b:fnExpr) => do
    let paramStr := BodyPat.toLean (← parsePat p)
    pure (.flatMap (← parseExpr r)
      (.lambda ⟨paramStr⟩ (← parseExpr b)))
  | `(fnExpr| $r:fnExpr ·map fun $p:fnPat =>
        $b:fnExpr) => do
    let paramStr := BodyPat.toLean (← parsePat p)
    pure (.map (← parseExpr r)
      (.lambda ⟨paramStr⟩ (← parseExpr b)))
  | `(fnExpr| $r:fnExpr ·map $fn:ident) => do
    recordIdentRef fn fn.getId
    pure (.map (← parseExpr r)
      (.var (toString fn.getId)))
  | `(fnExpr| $h:fnExpr :: $t:fnExpr) =>
    pure (.cons (← parseExpr h) (← parseExpr t))
  | `(fnExpr| $l:fnExpr ++ $r:fnExpr) =>
    pure (.append (← parseExpr l) (← parseExpr r))
  | `(fnExpr| Some $e:fnExpr) =>
    pure (.some_ (← parseExpr e))
  | `(fnExpr| None) => pure .none_
  | `(fnExpr| ⟨$args:fnExpr,*⟩) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.mkStruct "" as_.toList)
  | `(fnExpr| $n:ident ⟨$args:fnExpr,*⟩) => do
    recordIdentRef n n.getId
    let as_ ← args.getElems.mapM parseExpr
    pure (.mkStruct (toString n.getId) as_.toList)
  | `(fnExpr| $e:fnExpr ↦ $f:ident) => do
    let recv ← parseExpr e
    for qualified in (← resolveStructField (toString f.getId)) do
      recordIdentRef f qualified
    pure (.field recv (toString f.getId))
  | `(fnExpr| $r:fnExpr [ $f:ident => $v:fnExpr ]) => do
    let recv ← parseExpr r
    let val ← parseExpr v
    for qualified in (← resolveStructField (toString f.getId)) do
      recordIdentRef f qualified
    pure (.structUpdate recv
      (toString f.getId) val)
  | `(fnExpr| $e:fnExpr !! $i:fnExpr) =>
    pure (.index (← parseExpr e) (← parseExpr i))
  | `(fnExpr| $e:fnExpr ! $i:fnExpr) =>
    pure (.indexBang (← parseExpr e) (← parseExpr i))
  | `(fnExpr| . $n:ident) =>
    pure (.var s!".{n.getId}")
  | `(fnExpr| $fn:ident ‹ ›) => do
    -- Zero-arg call. `mapEmpty‹›` produces `.call (.var
    -- "mapEmpty") []`, which the Rust exporter renders as
    -- `map_empty()`; the bare-variable form `mapEmpty`
    -- would render as a function pointer.
    recordIdentRef fn fn.getId
    pure (.call (.var (toString fn.getId)) [])
  | `(fnExpr| $e:fnExpr ·foldlM $fn:ident
        $init:fnExpr) => do
    recordIdentRef fn fn.getId
    pure (.foldlM (.var (toString fn.getId))
      (← parseExpr init) (← parseExpr e))
  | `(fnExpr| $a:fnExpr < $b:fnExpr < $c:fnExpr) =>
    pure (.ineqChain [.lt, .lt] [← parseExpr a,
      ← parseExpr b, ← parseExpr c])
  | `(fnExpr| $a:fnExpr < $b:fnExpr ≤ $c:fnExpr) =>
    pure (.ineqChain [.lt, .le] [← parseExpr a,
      ← parseExpr b, ← parseExpr c])
  | `(fnExpr| $l:fnExpr < $r:fnExpr) =>
    pure (.lt (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $a:fnExpr ≤ $b:fnExpr ≤ $c:fnExpr ≤ $d:fnExpr) =>
    pure (.ineqChain [.le, .le, .le] [← parseExpr a,
      ← parseExpr b, ← parseExpr c, ← parseExpr d])
  | `(fnExpr| $a:fnExpr ≤ $b:fnExpr ≤ $c:fnExpr) =>
    pure (.ineqChain [.le, .le] [← parseExpr a,
      ← parseExpr b, ← parseExpr c])
  | `(fnExpr| $l:fnExpr ≤ $r:fnExpr) =>
    pure (.le (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr + $r:fnExpr) =>
    pure (.add (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr - $r:fnExpr) =>
    pure (.sub (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr * $r:fnExpr) =>
    pure (.mul (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr / $r:fnExpr) =>
    pure (.div (← parseExpr l) (← parseExpr r))
  | `(fnExpr| ∅) => pure .emptySet
  | `(fnExpr| ⦃ $e:fnExpr ⦄) =>
    pure (.setSingleton (← parseExpr e))
  | `(fnExpr| $l:fnExpr ∪ $r:fnExpr) =>
    pure (.setUnion (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $e:fnExpr ·setFlatMap fun $p:fnPat =>
        $b:fnExpr) => do
    let paramStr := BodyPat.toLean (← parsePat p)
    pure (.setFlatMap (← parseExpr e)
      paramStr (← parseExpr b))
  | `(fnExpr| $e:fnExpr ·forAll fun $p:ident =>
        $b:fnExpr) => do
    recordLocalBinder p p.getId
    pure (.setAll (← parseExpr e)
      (toString p.getId) (← parseExpr b))
  | `(fnExpr| $l:fnExpr ∈ $r:fnExpr) =>
    pure (.memberOf (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ∧ $r:fnExpr) =>
    pure (.and (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ‹break›∧ $r:fnExpr) =>
    pure (.and (.formatHint .breakAfter (← parseExpr l))
      (← parseExpr r))
  | `(fnExpr| $l:fnExpr ∨ $r:fnExpr) =>
    pure (.or (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr → $r:fnExpr) =>
    pure (.implies (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ‹break›→ $r:fnExpr) =>
    pure (.implies (.formatHint .breakAfter (← parseExpr l))
      (← parseExpr r))
  | `(fnExpr| ∀∀ $groups:fnForallGroup,* . $b:fnExpr) => do
    -- Each binder group is either a single untyped ident or
    -- one-or-more idents sharing a type via `∈ T`. The typed
    -- form additionally records `T` in the ident-ref tracker so
    -- the IDE-style cross-reference index stays accurate.
    let parsed ← groups.getElems.toList.mapM
      fun (g : Lean.TSyntax `fnForallGroup) =>
        match g with
        | `(fnForallGroup| $x:ident) => do
          recordLocalBinder x x.getId
          pure (([toString x.getId] : List String),
                (none : Option String))
        | `(fnForallGroup| $xs:ident* ∈ $t:ident) => do
          recordIdentRef t t.getId
          for x in xs do recordLocalBinder x x.getId
          let names := xs.toList.map
            fun (x : Lean.TSyntax `ident) => toString x.getId
          pure (names, some (toString t.getId))
        | _ => throwError s!"unexpected forall group"
    pure (.forall_ parsed (← parseExpr b))
  | `(fnExpr| sorry) => pure .sorryProof
  | `(fnExpr| proof[$t:term]) =>
    -- Reprint the parsed Lean term back to source form so the
    -- generated Lean export embeds it verbatim. The `term`
    -- syntax is a real Lean parse, so e.g. typos in identifier
    -- names surface as elaboration errors instead of slipping
    -- through as opaque strings. `reprint` returns `none` only
    -- for syntax that wasn't produced by the parser; in that
    -- corner case fall back to `toString` to keep elaboration
    -- moving (the resulting Lean source will still surface
    -- whatever's wrong).
    --
    -- Record the original term syntax so the in-tree DSL
    -- elaborator can graft user-source positions over the
    -- corresponding `dslProofMarker (…)` placeholder in the
    -- parsed-from-string syntax tree, restoring the source
    -- range Lean's `TermInfo` (and the InfoView) need to show
    -- the proof goal at the user's cursor.
    recordProofSyntax t.raw
    let s := t.raw.reprint.getD (toString t.raw)
    pure (.leanProof s.trimAscii.toString)
  | `(fnExpr| ‹break› $e:fnExpr) =>
    pure (.formatHint .break_ (← parseExpr e))
  | `(fnExpr| match $scrut:fnExpr with
        $arms:fnArm* end) => do
    let scrutAst ← parseExpr scrut
    let parsedArms ← arms.mapM fun arm =>
      match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat ;
            $p4:fnPat => $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2,
          ← parsePat p3, ← parsePat p4], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure ([← parsePat p], ← parseExpr rhs)
      | _ => Lean.Elab.throwUnsupportedSyntax
    let armsList := parsedArms.toList
    if DslLint.matchIsIrrefutable armsList then
      Lean.throwErrorAt scrut DslLint.irrefutableMatchMessage
    pure (.match_ scrutAst armsList)
  | `(fnExpr| match $h:ident : $scrut:fnExpr with
        $arms:fnArm* end) => do
    let scrutAst ← parseExpr scrut
    let parsedArms ← arms.mapM fun arm =>
      match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat ;
            $p4:fnPat => $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2,
          ← parsePat p3, ← parsePat p4], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure ([← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure ([← parsePat p], ← parseExpr rhs)
      | _ => Lean.Elab.throwUnsupportedSyntax
    let armsList := parsedArms.toList
    if DslLint.matchIsIrrefutable armsList then
      Lean.throwErrorAt scrut DslLint.irrefutableMatchMessage
    pure (.match_ scrutAst armsList
      (some (toString h.getId)))
  | `(fnExpr| let $p:fnPat := $v:fnExpr ; $b:fnExpr) => do
    pure (.letIn (← parsePat p)
      (← parseExpr v) (← parseExpr b))
  | `(fnExpr| let $p:fnPat ← $v:fnExpr ; $b:fnExpr) => do
    pure (.letBindIn (← parsePat p)
      (← parseExpr v) (← parseExpr b))
  | `(fnExpr| if $c:fnExpr then $t:fnExpr else $e:fnExpr) =>
    pure (.ifThenElse (← parseExpr c) (← parseExpr t)
      (← parseExpr e))
  | `(fnExpr| $l:fnExpr ≠ $r:fnExpr) =>
    pure (.neq (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr == $r:fnExpr) =>
    pure (.eq (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr = $r:fnExpr) =>
    pure (.propEq (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $e:fnExpr ·any fun $p:fnPat =>
        $b:fnExpr) => do
    let paramStr := BodyPat.toLean (← parsePat p)
    pure (.anyList (← parseExpr e) paramStr
      (← parseExpr b))
  | _ => Lean.Elab.throwUnsupportedSyntax

/-- Fold a sequence of `fnStmt` syntax nodes followed by a
    return expression into a chained `letIn`/`letBindIn`
    `DslExpr`. -/
def parseStmtsAsExpr
    (stmts : Array Lean.Syntax) (ret : DslExpr)
    : Lean.Elab.Command.CommandElabM DslExpr := do
  let mut acc := ret
  for stx in stmts.reverse do
    match stx with
    | `(fnStmt| let $p:fnPat := $e:fnExpr) =>
      acc := .letIn (← parsePat p) (← parseExpr e) acc
    | `(fnStmt| let $p:fnPat ← $e:fnExpr) =>
      acc := .letBindIn (← parsePat p)
        (← parseExpr e) acc
    | _ => Lean.Elab.throwUnsupportedSyntax
  pure acc

def parseFnParam
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.TSyntax `term
         × Lean.Syntax) := do
  match stx with
  | `(fnParam| ($n:ident $d:term : $t:term)) =>
    pure (n, d, t)
  | _ => Lean.Elab.throwUnsupportedSyntax

def parsePrecond
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM Precondition := do
  match stx with
  | `(fnPrecond| $e:fnExpr using [ $lemmas:ident,* ]) =>
    let parsed ← parseExpr e
    let lemmaNames :=
      lemmas.getElems.toList.map (toString ·.getId)
    -- Mirror the recovery the bare-`fnExpr` arm performs:
    -- a property-call written as bracketless `Name args …`
    -- still lowers to `.named` so the generated proof
    -- binder stays `h_<Name>`.
    match parsed with
    | .call (.var name) args =>
      let bareArgs := args.foldr
        (fun arg acc => match arg, acc with
          | .var n, some xs => some (n :: xs)
          | _, _ => none)
        (some [])
      match bareArgs with
      | some xs => pure (.named name xs lemmaNames)
      | none => pure (.expr_ parsed lemmaNames)
    | _ => pure (.expr_ parsed lemmaNames)
  | `(fnPrecond| $e:fnExpr) =>
    -- Bracketless property-call form `Name arg₁ arg₂ …`
    -- (the only form now that the legacy `Name(args)`
    -- parenthesised syntax is gone): `parseExpr` lowers it to
    -- a `.call` whose head is `.var Name` and whose args are
    -- bare `.var argᵢ`. Re-interpret that as a `.named`
    -- precondition so the auto-generated proof binder stays
    -- `h_<Name>` rather than the generic `h_pre<i>`.
    let parsed ← parseExpr e
    match parsed with
    | .call (.var name) args =>
      let bareArgs := args.foldr
        (fun arg acc => match arg, acc with
          | .var n, some xs => some (n :: xs)
          | _, _ => none)
        (some [])
      match bareArgs with
      | some xs => pure (.named name xs)
      | none => pure (.expr_ parsed)
    | _ => pure (.expr_ parsed)
  | _ => Lean.Elab.throwUnsupportedSyntax

-- ══════════════════════════════════════════════
-- Core elaboration helpers
-- ══════════════════════════════════════════════

/-- Normalise a Lean type string for def generation.
    Maps DSL-only types (e.g. `Set T`) to their Lean
    equivalents (e.g. `List T`). -/
private def normaliseLeanType (s : String) : String :=
  (DSLType.parse s).toLean

def buildFnType
    (paramData : Array (Lean.Ident × Lean.TSyntax `term
      × Lean.Syntax))
    (retTy : Lean.TSyntax `term)
    : Lean.Elab.Command.CommandElabM String := do
  let paramTypeStrs := paramData.map fun (_, _, pt) =>
    let raw := if pt.isIdent then toString pt.getId
      else pt.reprint.getD (toString pt)
    normaliseLeanType raw
  let retRepr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  pure (" → ".intercalate paramTypeStrs.toList
    ++ s!" → {normaliseLeanType retRepr}")

/-- Syntactic header for a `defFn`: the function name
    together with the user-supplied symbol and top-level
    doc-string `Doc` terms. -/
structure FnDefHeader where
  name : Lean.Ident
  symDoc : Lean.TSyntax `term
  doc : Lean.TSyntax `term

open Lean Elab Command in
/-- Parse the optional display-template syntax attached to a
    `defFn`. Each `displayPart` references parameters by name
    via `#paramName`; the parameter's auto-looked-up
    `symbolDoc` is used when no explicit symbol is given. -/
def parseFnDisplay
    (paramData : Array (Lean.Ident × Lean.TSyntax `term
      × Lean.Syntax))
    (dps : Lean.TSyntaxArray `displayPart)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  let argTypes : List (String × String) :=
    paramData.toList.map fun (pn, _, pt) =>
      let tyStr :=
        if pt.isIdent then toString pt.getId
        else pt.reprint.getD (toString pt)
      (toString pn.getId, tyStr)
  -- A `defFn` is not self-referential in the way enum
  -- variants are, so `selfName`/`selfSym` are unused;
  -- pass dummy values that won't be matched.
  let dummySym : Lean.TSyntax `term ←
    `((MathDoc.raw ""))
  let dpDefs ← dps.mapM
    (parseDisplayPart argTypes "" dummySym [])
  `([$[$dpDefs],*])

/-- Whether a free identifier reference to `name` appears
    anywhere inside `stx`. Used by `buildFnDef` to skip
    let-bindings for parameter names that the user's `doc!`
    string never references — keeps the generated `def` clear
    of unused-variable linter warnings. -/
private partial def hasIdentRef (stx : Lean.Syntax)
    (name : Lean.Name) : Bool :=
  if stx.isIdent && stx.getId == name then true
  else stx.getArgs.any (hasIdentRef · name)

open Lean Elab Command in
def buildFnDef
    (hdr : FnDefHeader)
    (paramData : Array (Ident × TSyntax `term
      × Syntax))
    (retTy : TSyntax `term)
    (body : TSyntax `term)
    (preconds : List Precondition := [])
    (postconds : List Postcondition := [])
    (mutualGroup : Option String := none)
    (display : Option (TSyntax `term) := none)
    (isImplicit : Bool := false)
    : CommandElabM Unit := do
  let name := hdr.name
  let symDoc := hdr.symDoc
  -- Make each parameter name available as a `Doc.code "<name>"`
  -- in scope of the user's `doc` term, so a `doc!` description
  -- can interpolate parameter references via `{paramName}` —
  -- e.g. `defFn nodeNeighbors (doc! "All nodes {a} reaches in
  -- {pd}.") (pd : …) (a : …)`. The `Doc.code` binding (rather
  -- than `Doc.plain`) preserves the prior `\texttt{…}` rendering
  -- for parameter references in `defFn` docs, where prose
  -- traditionally typesets parameter names in monospace.
  let mut doc := hdr.doc
  for (pn, _, _) in paramData.reverse do
    let pname := pn.getId
    if hasIdentRef hdr.doc.raw pname then
      let pns : TSyntax `term :=
        quote (toString pname)
      doc ← `(let $pn:ident : Doc := Doc.code $pns; $doc)
  if isImplicit && paramData.size != 1 then
    Lean.throwErrorAt name
      m!"an `implicit` defFn must take exactly one explicit \
        argument (so call sites can render as that argument \
        alone); got {paramData.size}"
  let paramDefs ← paramData.mapM
    fun (pn, pd, pt) => do
      let ns : TSyntax `term :=
        quote (toString pn.getId)
      let typeStr :=
        if pt.isIdent then toString pt.getId
        else pt.reprint.getD (toString pt)
      let tyTerm ← `(DSLType.parse $(quote typeStr))
      `({ name := $ns, ty := $tyTerm,
          doc := ($pd : Doc) : FieldDef })
  let ns : TSyntax `term :=
    quote (toString name.getId)
  let retStr :=
    if retTy.raw.isIdent
    then toString retTy.raw.getId
    else retTy.raw.reprint.getD (toString retTy)
  let retTn ← `(DSLType.parse $(quote retStr))
  let paramList ← `([$[$paramDefs],*])
  let precondList : TSyntax `term := quote preconds
  let postcondList : TSyntax `term := quote postconds
  let mutualGroupTerm : TSyntax `term := quote mutualGroup
  let displayTerm : TSyntax `term ← match display with
    | some dpList => `((some $dpList : Option (List DisplayPart)))
    | none => `((none : Option (List DisplayPart)))
  let isImplicitTerm : TSyntax `term := quote isImplicit
  -- Capture the last component of the source-level `namespace`
  -- enclosing this `defFn` so the Lean export can prefer it over
  -- the first-parameter-type heuristic for placing the function.
  let curr ← getCurrNamespace
  let sourceNs : Option String := match curr with
    | .anonymous => none
    | _ => curr.components.getLast?.map toString
  let sourceNsTerm : TSyntax `term := quote sourceNs
  let fnDefId := mkIdent (name.getId ++ `fnDef)
  elabCommand (← `(command|
    def $fnDefId : FnDef :=
      { name := $ns,
        symbolDoc := ($symDoc : Doc),
        doc := ($doc : Doc),
        params := $paramList,
        returnType := $retTn,
        preconditions := $precondList,
        postconditions := $postcondList,
        body := $body,
        mutualGroup := $mutualGroupTerm,
        display := $displayTerm,
        sourceNamespace := $sourceNsTerm,
        isImplicit := $isImplicitTerm }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerFnDef $fnDefId $modName))

/-- Build precondition proof parameter strings for
    the generated Lean def. A named `prop(a, b)` becomes
    `(h_prop : prop a b)`; an expression-form precondition
    becomes `(h_pre<i> : <expr>)`, where `<i>` is its
    positional index among the function's preconditions. -/
private def precondParamBinds
    (preconds : List Precondition)
    : String :=
  " ".intercalate
    (preconds.zipIdx.map fun (pc, i) => match pc with
      | .named n args _ =>
        let argStr := " ".intercalate args
        s!"(h_{n} : {n} {argStr})"
      | .expr_ e _ =>
        s!"(h_pre{i} : {e.toLean})")

/-- Render a postcondition as a Lean source-level expression,
    used inside the subtype return wrapper. -/
private def postcondLean : Postcondition → String
  | .named n args =>
    if args.isEmpty then n
    else s!"{n} {" ".intercalate args}"
  | .expr_ e => e.toLean

/-- Build the conjunction of postcondition applications
    used as the predicate inside the subtype return type. -/
private def postcondPredicate
    (postconds : List Postcondition)
    : String :=
  " ∧ ".intercalate (postconds.map postcondLean)

/-- Wrap a return type in the postcondition subtype
    `\{ result : RetTy // P₁ ∧ P₂ ∧ … }` when postconds
    are present; otherwise return the raw return type. -/
private def wrapRetType
    (retTy : String)
    (postconds : List Postcondition)
    : String :=
  if postconds.isEmpty then retTy
  else s!"\{ result : {retTy} // {postcondPredicate postconds} }"

/-- Wrap a body expression with the subtype anonymous
    constructor `⟨body, <proof>⟩` when postconds are present;
    otherwise return the body unchanged. The proof tactic
    starts with `decide` so postconds that hold by computation
    on the literal body discharge cleanly (no `sorry` warning);
    when `decide` fails or doesn't apply, it falls back to
    `sorry` to keep the build going. -/
private def wrapBody
    (body : String) (postconds : List Postcondition)
    : String :=
  if postconds.isEmpty then body
  else s!"⟨{body}, by first | trivial | decide | sorry⟩"

/-- Lean proof tactic for a self-recursive call's
    precondition obligation. Tries each `using [lemma, …]`
    lemma via `apply` (after `assumption`) so forall-quantified
    preservation lemmas — whose conclusion unifies with the
    goal but whose premises need hypotheses outside the simp
    set — succeed before falling back to `simp_all` with the
    same lemmas spliced in. -/
private def precondProof : Precondition → String
  | .named n _ extras =>
    let applyAlts :=
      extras.map fun l => s!"apply {l}"
    let simpAlt :=
      let ls := String.intercalate ", " (n :: extras)
      s!"simp_all [{ls}]"
    let alts := "assumption" :: applyAlts ++ [simpAlt]
    s!"(by first | {String.intercalate " | " alts})"
  | .expr_ _ extras =>
    let applyAlts :=
      extras.map fun l => s!"apply {l}"
    let simpAlt :=
      if extras.isEmpty then "simp_all"
      else s!"simp_all [{String.intercalate ", " extras}]"
    let alts := "assumption" :: applyAlts ++ [simpAlt]
    s!"(by first | {String.intercalate " | " alts})"

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $[implicit%$impl?]? $[@[ $attrs?:ident,* ]]?
       $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam* $[displayed ( $dps:displayPart,* )]?
       $[requires $reqs:fnPrecond,*]?
       $[ensures $ens:fnPrecond,*]?
       : $retTy:term where
       $arms:fnArm*) => do
    let isImplicit := impl?.isSome
    let attrPrefix := match attrs? with
      | some xs =>
        let names := xs.getElems.toList.map
          (fun (a : Lean.TSyntax `ident) => toString a.getId)
        s!"@[{", ".intercalate names}]\n"
      | none => ""
    DslLint.lintDocTerm doc
    identRefBuffer.set #[]
    -- Reset the proof-syntax buffer so this `defFn`'s
    -- `proof[…]` bodies are collected from a clean slate
    -- and consumed in source order by `graftDslProofMarkers`
    -- below.
    proofSyntaxBuffer.set #[]
    -- Reset the local-binder buffer so this `defFn`'s param
    -- and `let`-binding ident syntaxes are collected from a
    -- clean slate and consumed in source order by
    -- `graftLocalIdents` below.
    localBinderBuffer.set #[]
    let paramData ← ps.mapM parseFnParam
    -- Each parameter binder needs its user-source ident
    -- syntax recorded so the rendered defStr's binder
    -- occurrence (and every body usage) can be grafted with
    -- user positions, lighting up LSP gotoDef.
    for (pn, _, _) in paramData do
      recordLocalBinder pn pn.getId
    for (_, _, ty) in paramData do recordTypeIdents ty
    recordTypeIdents retTy
    let displayTerm ← match dps with
      | some d => Option.some <$> parseFnDisplay paramData d.getElems
      | none => pure none
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM
          (parsePrecond ·.raw)
      | none => pure []
    let postconds : List Postcondition ←
      match ens with
      | some pcs =>
        (·.map Precondition.toPostcondition) <$>
          pcs.getElems.toList.mapM
            (parsePrecond ·.raw)
      | none => pure []
    let parsed ← arms.mapM fun arm => match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat ;
            $p4:fnPat => $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2,
          ← parsePat p3, ← parsePat p4], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure (#[← parsePat p], ← parseExpr rhs)
      | _ => throwError "invalid fnArm"
    let armsList : List (List BodyPat × DslExpr) :=
      parsed.toList.map fun (a, r) => (a.toList, r)
    if DslLint.matchIsIrrefutable armsList then
      Lean.throwErrorAt name DslLint.irrefutableWhereMessage
    -- Generate Lean def via string parsing.
    -- `withProofMarkers := true` wraps each `proof[…]` body in
    -- a `dslProofMarker` placeholder so `graftDslProofMarkers`
    -- below can splice the user-source `proof[…]` syntax back
    -- in over the parsed-from-string copy — that restores the
    -- source positions Lean's `TermInfo` (and the InfoView)
    -- need to surface the proof goal at the user's cursor.
    let fnNameStr := toString name.getId
    let precondProofs := preconds.map precondProof
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        let rhsStr := wrapBody
          (rhsAst.toLeanWith fnNameStr precondProofs
            (withProofMarkers := true)) postconds
        s!"  | {patStr} => {rhsStr}"
    let defKw := "def"
    let paramNames := paramData.toList.map
      fun (pn, _, _) => toString pn.getId
    let defStr ←
      if preconds.isEmpty && postconds.isEmpty then
        let tyStr ← buildFnType paramData retTy
        pure s!"{attrPrefix}{defKw} {name.getId} : {tyStr}\n\
          {"\n".intercalate armStrs}"
      else do
        let paramBinds := " ".intercalate
          (paramData.toList.map fun (pn, _, pt) =>
            let tyStr :=
              if pt.isIdent then toString pt.getId
              else pt.reprint.getD (toString pt)
            s!"({pn.getId} : {normaliseLeanType tyStr})")
        let precBinds := precondParamBinds preconds
        let retRaw :=
          if retTy.raw.isIdent
          then toString retTy.raw.getId
          else retTy.raw.reprint.getD (toString retTy)
        let retRepr := wrapRetType
          (normaliseLeanType retRaw) postconds
        let matchArgs := ", ".intercalate paramNames
        pure s!"{attrPrefix}{defKw} {name.getId} \
          {paramBinds} {precBinds} : {retRepr} :=\n\
          match {matchArgs} with\n\
          {"\n".intercalate armStrs}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx =>
      let stx := graftUserNameToken name.getId name.raw stx
      -- Splice each user-source `proof[…]` body back in over
      -- its `dslProofMarker (…)` placeholder so Lean's
      -- elaborator records `TermInfo` at the user's positions.
      let userProofs ← takeProofSyntaxes
      let (stx, _) := graftDslProofMarkers userProofs stx
      -- Splice each parameter binder, `let`-binding, and
      -- variable usage's user-source syntax in over the
      -- corresponding rendered ident, so LSP gotoDef on a
      -- local-var usage in the DSL source navigates to its
      -- binder rather than dead-ending at synthetic positions.
      let stx ← graftLocalIdentsFromBuffers stx
      elabCommand stx
    | .error e =>
      -- Drop any buffered proof syntaxes / local binders so a
      -- later `defFn` doesn't inherit stale entries.
      let _ ← takeProofSyntaxes
      let _ ← takeLocalBinders
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    setUserDeclRanges name (← getRef)
    -- Build FnBody metadata
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quote rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildFnDef ⟨name, symDoc, doc⟩ paramData retTy
      bodyTerm preconds postconds (display := displayTerm)
      (isImplicit := isImplicit)
    flushIdentRefs

-- ══════════════════════════════════════════════
-- Direct expression form
-- ══════════════════════════════════════════════

open Lean Elab Command in
elab_rules : command
  | `(defFn $[implicit%$impl?]? $[@[ $attrs?:ident,* ]]?
       $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam* $[displayed ( $dps:displayPart,* )]?
       $[requires $reqs:fnPrecond,*]?
       $[ensures $ens:fnPrecond,*]?
       : $retTy:term := $rhs:fnExpr) => do
    let isImplicit := impl?.isSome
    let attrPrefix := match attrs? with
      | some xs =>
        let names := xs.getElems.toList.map
          (fun (a : Lean.TSyntax `ident) => toString a.getId)
        s!"@[{", ".intercalate names}]\n"
      | none => ""
    DslLint.lintDocTerm doc
    identRefBuffer.set #[]
    proofSyntaxBuffer.set #[]
    localBinderBuffer.set #[]
    let paramData ← ps.mapM parseFnParam
    for (pn, _, _) in paramData do
      recordLocalBinder pn pn.getId
    for (_, _, ty) in paramData do recordTypeIdents ty
    recordTypeIdents retTy
    let displayTerm ← match dps with
      | some d => Option.some <$> parseFnDisplay paramData d.getElems
      | none => pure none
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM
          (parsePrecond ·.raw)
      | none => pure []
    let postconds : List Postcondition ←
      match ens with
      | some pcs =>
        (·.map Precondition.toPostcondition) <$>
          pcs.getElems.toList.mapM
            (parsePrecond ·.raw)
      | none => pure []
    let rhsAst ← parseExpr rhs
    let fnNameStr := toString name.getId
    let precondProofs := preconds.map precondProof
    let rhsStr := wrapBody
      (rhsAst.toLeanWith fnNameStr precondProofs
        (withProofMarkers := true)) postconds
    let paramBinds := " ".intercalate
      (paramData.toList.map fun (pn, _, pt) =>
        let tyStr :=
          if pt.isIdent then toString pt.getId
          else pt.reprint.getD (toString pt)
        s!"({pn.getId} : {normaliseLeanType tyStr})")
    let precBinds := precondParamBinds preconds
    let retRaw :=
      if retTy.raw.isIdent
      then toString retTy.raw.getId
      else retTy.raw.reprint.getD (toString retTy)
    let retRepr := wrapRetType
      (normaliseLeanType retRaw) postconds
    let defStr :=
      s!"{attrPrefix}def {name.getId} {paramBinds} \
         {precBinds} : {retRepr} :=\n  {rhsStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx =>
      let stx := graftUserNameToken name.getId name.raw stx
      let userProofs ← takeProofSyntaxes
      let (stx, _) := graftDslProofMarkers userProofs stx
      let stx ← graftLocalIdentsFromBuffers stx
      elabCommand stx
    | .error e =>
      let _ ← takeProofSyntaxes
      let _ ← takeLocalBinders
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    setUserDeclRanges name (← getRef)
    let bodyTerm ←
      `(FnBody.expr $(quote rhsAst))
    buildFnDef ⟨name, symDoc, doc⟩ paramData retTy
      bodyTerm preconds postconds (display := displayTerm)
      (isImplicit := isImplicit)
    flushIdentRefs

-- ══════════════════════════════════════════════
-- Mutual form
-- ══════════════════════════════════════════════

/-- One entry of a `defFnMutual` group. Same syntax as the
    pattern-matching form of `defFn` but parsed inside the
    mutual-group command. -/
declare_syntax_cat mutualFnEntry
syntax "defFn " ident "(" term ")" "(" term ")"
    fnParam* ("displayed " "(" displayPart,+ ")")?
    ("requires " fnPrecond,+)?
    ("ensures " fnPrecond,+)?
    ":" term " where" fnArm*
    : mutualFnEntry

/-- A group of mutually-recursive pattern-matching
    `defFn`s, enclosed in `defFnMutual … end` and emitted as
    a single `mutual … end` block to the Lean backend. Each
    entry is individually registered with the DSL registry. -/
syntax "defFnMutual" mutualFnEntry+ "end" : command

/-- Parsed result for one mutual entry: the generated `def …`
    string plus the syntactic pieces needed to register the
    `FnDef` entry. -/
private structure MutualEntryResult where
  defStr : String
  name : Lean.Ident
  symDoc : Lean.TSyntax `term
  doc : Lean.TSyntax `term
  paramData : Array (Lean.Ident × Lean.TSyntax `term
    × Lean.Syntax)
  retTy : Lean.TSyntax `term
  preconds : List Precondition
  postconds : List Postcondition
  parsed : Array (Array BodyPat × DslExpr)
  display : Option (Lean.TSyntax `term)

open Lean Elab Command Term in
private def parseMutualEntry
    (entry : Lean.TSyntax `mutualFnEntry)
    : CommandElabM MutualEntryResult := do
  match entry with
  | `(mutualFnEntry|
        defFn $name:ident ($symDoc:term) ($doc:term)
          $ps:fnParam* $[displayed ( $dps:displayPart,* )]?
          $[requires $reqs:fnPrecond,*]?
          $[ensures $ens:fnPrecond,*]?
          : $retTy:term where
          $arms:fnArm*) => do
    DslLint.lintDocTerm doc
    let paramData ← ps.mapM parseFnParam
    for (pn, _, _) in paramData do
      recordLocalBinder pn pn.getId
    for (_, _, ty) in paramData do recordTypeIdents ty
    recordTypeIdents retTy
    let displayTerm ← match dps with
      | some d => Option.some <$> parseFnDisplay paramData d.getElems
      | none => pure none
    let preconds ← match reqs with
      | some pcs =>
        pcs.getElems.toList.mapM (parsePrecond ·.raw)
      | none => pure []
    let postconds : List Postcondition ←
      match ens with
      | some pcs =>
        (·.map Precondition.toPostcondition) <$>
          pcs.getElems.toList.mapM (parsePrecond ·.raw)
      | none => pure []
    let parsed ← arms.mapM fun arm => match arm with
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat ;
            $p4:fnPat => $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2,
          ← parsePat p3, ← parsePat p4], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat ; $p3:fnPat
            => $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2,
          ← parsePat p3], ← parseExpr rhs)
      | `(fnArm| | $p1:fnPat ; $p2:fnPat =>
            $rhs:fnExpr) => do
        pure (#[← parsePat p1, ← parsePat p2],
          ← parseExpr rhs)
      | `(fnArm| | $p:fnPat => $rhs:fnExpr) => do
        pure (#[← parsePat p], ← parseExpr rhs)
      | _ => throwError "invalid fnArm"
    let armsList : List (List BodyPat × DslExpr) :=
      parsed.toList.map fun (a, r) => (a.toList, r)
    if DslLint.matchIsIrrefutable armsList then
      Lean.throwErrorAt name DslLint.irrefutableWhereMessage
    let fnNameStr := toString name.getId
    let precondProofs := preconds.map precondProof
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        let rhsStr := wrapBody
          (rhsAst.toLeanWith fnNameStr precondProofs
            (withProofMarkers := true)) postconds
        s!"  | {patStr} => {rhsStr}"
    let defStr ←
      if preconds.isEmpty && postconds.isEmpty then
        let tyStr ← buildFnType paramData retTy
        pure s!"def {name.getId} : {tyStr}\n\
          {"\n".intercalate armStrs}"
      else do
        let paramBinds := " ".intercalate
          (paramData.toList.map fun (pn, _, pt) =>
            let tyStr :=
              if pt.isIdent then toString pt.getId
              else pt.reprint.getD (toString pt)
            s!"({pn.getId} : {normaliseLeanType tyStr})")
        let precBinds := precondParamBinds preconds
        let retRaw :=
          if retTy.raw.isIdent
          then toString retTy.raw.getId
          else retTy.raw.reprint.getD (toString retTy)
        let retRepr := wrapRetType
          (normaliseLeanType retRaw) postconds
        let paramNames := paramData.toList.map
          fun (pn, _, _) => toString pn.getId
        let matchArgs := ", ".intercalate paramNames
        pure s!"def {name.getId} \
          {paramBinds} {precBinds} : {retRepr} :=\n\
          match {matchArgs} with\n\
          {"\n".intercalate armStrs}"
    pure { defStr, name, symDoc, doc, paramData, retTy,
           preconds, postconds, parsed,
           display := displayTerm }
  | _ => throwError "invalid mutualFnEntry"

open Lean Elab Command Term in
elab_rules : command
  | `(defFnMutual $entries:mutualFnEntry* end) => do
    identRefBuffer.set #[]
    proofSyntaxBuffer.set #[]
    localBinderBuffer.set #[]
    if entries.isEmpty then
      throwError "defFnMutual: expected at least one entry"
    let results ← entries.mapM parseMutualEntry
    let mutualStr :=
      "mutual\n"
        ++ "\n".intercalate (results.toList.map (·.defStr))
        ++ "\nend"
    let env ← getEnv
    match Parser.runParserCategory env `command
      mutualStr with
    | .ok stx =>
      -- Graft each entry's user-source name into the parsed
      -- mutual block so binder TermInfos point at the user's
      -- file rather than synthetic positions inside `mutualStr`.
      let stx := results.foldl
        (fun s r => graftUserNameToken r.name.getId r.name.raw s)
        stx
      let userProofs ← takeProofSyntaxes
      let (stx, _) := graftDslProofMarkers userProofs stx
      let stx ← graftLocalIdentsFromBuffers stx
      elabCommand stx
    | .error e =>
      let _ ← takeProofSyntaxes
      let _ ← takeLocalBinders
      throwError s!"defFnMutual: parse error: {e}\n\
        ---\n{mutualStr}\n---"
    -- Tag every entry with a shared group id derived from
    -- the first entry's name, so the Lean backend can emit
    -- them inside a single `mutual … end` block.
    let groupTag ← match results[0]? with
      | some r => pure s!"{r.name.getId}"
      | none => throwError "defFnMutual: expected at least one entry"
    for (entry, r) in entries.zip results do
      setUserDeclRanges r.name entry.raw
      let armDefs ← r.parsed.mapM
        fun (patAst, rhsAst) => do
          let pq : TSyntax `term := quote patAst.toList
          let rq : TSyntax `term := quote rhsAst
          `({ pat := $pq, rhs := $rq : BodyArm })
      let armList ← `([$[$armDefs],*])
      let bodyTerm ← `(FnBody.matchArms $armList)
      buildFnDef ⟨r.name, r.symDoc, r.doc⟩ r.paramData
        r.retTy bodyTerm r.preconds r.postconds
        (mutualGroup := some groupTag)
        (display := r.display)
    flushIdentRefs
