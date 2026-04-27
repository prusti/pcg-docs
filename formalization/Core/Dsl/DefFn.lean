import Core.Registry
import Core.Export.Lean
import Core.Dsl.DefEnum
import Runtime
import Lean

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
syntax "[" "]" : fnExpr
syntax "[" fnExpr,+ "]" : fnExpr
syntax num : fnExpr
syntax ident : fnExpr
syntax "(" fnExpr ")" : fnExpr
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
syntax "⟨" fnExpr,+ "⟩" : fnExpr
-- Named struct constructor: Name⟨a, b⟩
syntax ident "⟨" fnExpr,+ "⟩" : fnExpr
-- Field access chain: expr ↦ name
syntax fnExpr "↦" ident : fnExpr
-- Functional struct update: expr[field => newValue].
-- Returns a copy of `expr` with `field` replaced.
syntax fnExpr "[" ident " => " fnExpr "]" : fnExpr
-- Fallible indexing: expr !! expr (for list[idx]?)
syntax fnExpr "!!" fnExpr : fnExpr
-- Infallible indexing: expr ! expr (for list[idx])
syntax fnExpr "!" fnExpr : fnExpr
-- Function call: fn ‹ arg1, arg2 ›
syntax ident "‹" fnExpr,* "›" : fnExpr
-- Dot-prefixed nullary variant: .leaf
syntax "." ident : fnExpr
-- Dot-prefixed applied variant: .leaf ‹arg1, arg2›
syntax "." ident "‹" fnExpr,* "›" : fnExpr
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
-- Set/list membership: expr ∈ expr
syntax fnExpr " ∈ " fnExpr : fnExpr
-- Logical conjunction: expr ∧ expr
syntax fnExpr " ∧ " fnExpr : fnExpr
-- Logical disjunction: expr ∨ expr
syntax fnExpr " ∨ " fnExpr : fnExpr
-- Implication: expr → expr
syntax fnExpr " → " fnExpr : fnExpr
-- Universal quantifier: ∀ ident, expr
syntax "∀∀" ident "," fnExpr : fnExpr
-- Proof placeholder
syntax "sorry" : fnExpr
-- Raw Lean proof term (invisible in Rust/LaTeX)
syntax "lean_proof(" str ")" : fnExpr

declare_syntax_cat fnArm
syntax "| " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat " => " fnExpr : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat " => " fnExpr
    : fnArm
syntax "| " fnPat "; " fnPat "; " fnPat "; " fnPat
    " => " fnExpr : fnArm

-- Match expression: match expr with | pat => expr end
syntax "match " fnExpr " with" fnArm+ " end" : fnExpr

-- If-then-else expression: if cond then t else e
syntax "if " fnExpr " then " fnExpr " else " fnExpr : fnExpr
-- Inequality: expr ≠ expr
syntax fnExpr " ≠ " fnExpr : fnExpr
-- Equality: expr == expr
syntax fnExpr " == " fnExpr : fnExpr
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
syntax ident "(" ident,+ ")" : fnPrecond

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
syntax "defFn " ident "(" term ")" "(" term ")"
    fnParam* ("displayed " "(" displayPart,+ ")")?
    ("requires " fnPrecond,+)?
    ":" term " where" fnArm* : command

/-- Direct expression function (no pattern match). See the
    pattern-matching form for the optional `displayed` clause. -/
syntax "defFn " ident "(" term ")" "(" term ")"
    fnParam* ("displayed " "(" displayPart,+ ")")?
    ("requires " fnPrecond,+)?
    ":" term " :=" fnExpr : command

-- ══════════════════════════════════════════════
-- Parsing helpers
-- ══════════════════════════════════════════════

-- Buffer of `(identifierSyntax, name)` pairs collected while
-- parsing a `defFn` body. After the generated Lean `def` has
-- been elaborated, each pair whose name resolves to a constant
-- in the environment is replayed as a `TermInfo` leaf, so the
-- LSP can offer go-to-definition and hover for DSL-level
-- identifiers (e.g. `initStateCapability` in `treeCapability`'s
-- body). We use a module-level `IO.Ref` rather than threading
-- state through `parseExpr`/`parsePat` because `parseExpr` is
-- partial and mutually called from many places.
private initialize identRefBuffer :
    IO.Ref (Array (Lean.Syntax × Lean.Name)) ← IO.mkRef #[]

/-- Record an identifier reference for later `TermInfo`
    emission. Called from the parser whenever an `ident` token
    syntactically denotes a potential global reference
    (function call head, free variable, struct/enum
    constructor, higher-order function argument, ...). -/
private def recordIdentRef (stx : Lean.Syntax)
    (name : Lean.Name) : IO Unit :=
  identRefBuffer.modify (·.push (stx, name))

/-- Walk a type-position `Syntax` tree and record every
    identifier inside it via `recordIdentRef`, so the LSP can
    jump from a type name in a `defFn` parameter or return
    type (e.g. `Body` in `(body : Body)`) to the corresponding
    struct/enum/alias definition. -/
private partial def recordTypeIdents
    (stx : Lean.Syntax) : IO Unit := do
  if stx.isIdent then
    recordIdentRef stx stx.getId
  else
    for arg in stx.getArgs do
      recordTypeIdents arg

/-- Take the currently-buffered identifier references and
    empty the buffer, so subsequent `defFn` invocations start
    from a clean slate. -/
private def takeIdentRefs :
    IO (Array (Lean.Syntax × Lean.Name)) := do
  let refs ← identRefBuffer.get
  identRefBuffer.set #[]
  return refs

open Lean Elab Command in
/-- Push a `TermInfo` leaf for each recorded identifier whose
    name resolves to an existing constant, so the LSP can jump
    from a DSL-level identifier to the backing Lean
    definition. Resolution respects the current namespace and
    any `open` declarations in scope, so e.g.
    `writeBytesAt` inside `namespace Memory` correctly
    resolves to `Memory.writeBytesAt`. Identifiers that don't
    resolve (locally bound variables, forward references
    inside a mutual group that hasn't been elaborated yet,
    ...) are silently skipped. -/
private def flushIdentRefs : CommandElabM Unit := do
  let refs ← takeIdentRefs
  let env ← getEnv
  let ns ← getCurrNamespace
  let opens ← getOpenDecls
  let opts ← getOptions
  for (stx, name) in refs do
    let candidates :=
      Lean.ResolveName.resolveGlobalName env opts ns opens name
    let resolved := candidates.filterMap fun (n, parts) =>
      if parts.isEmpty && env.contains n then some n else none
    match resolved with
    | [n] => addConstInfo stx n
    | _ => pure ()

mutual
partial def parsePatAtom
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM BodyPat := do
  match stx with
  | `(fnPatAtom| _) => pure .wild
  | `(fnPatAtom| $n:ident) => pure (.var (toString n.getId))
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
  | `(fnPat| $n:ident) =>
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
  | `(fnExpr| $r:fnExpr · $m:ident) =>
    pure (.dot (← parseExpr r)
      (toString m.getId))
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
  | `(fnExpr| $e:fnExpr ↦ $f:ident) =>
    pure (.field (← parseExpr e) (toString f.getId))
  | `(fnExpr| $r:fnExpr [ $f:ident => $v:fnExpr ]) =>
    pure (.structUpdate (← parseExpr r)
      (toString f.getId) (← parseExpr v))
  | `(fnExpr| $e:fnExpr !! $i:fnExpr) =>
    pure (.index (← parseExpr e) (← parseExpr i))
  | `(fnExpr| $e:fnExpr ! $i:fnExpr) =>
    pure (.indexBang (← parseExpr e) (← parseExpr i))
  | `(fnExpr| $fn:ident ‹ $args:fnExpr,* ›) => do
    recordIdentRef fn fn.getId
    let as_ ← args.getElems.mapM parseExpr
    pure (.call (.var (toString fn.getId)) as_.toList)
  | `(fnExpr| . $n:ident ‹ $args:fnExpr,* ›) => do
    let as_ ← args.getElems.mapM parseExpr
    pure (.call (.var s!".{n.getId}") as_.toList)
  | `(fnExpr| . $n:ident) =>
    pure (.var s!".{n.getId}")
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
    pure (.setAll (← parseExpr e)
      (toString p.getId) (← parseExpr b))
  | `(fnExpr| $l:fnExpr ∈ $r:fnExpr) =>
    pure (.memberOf (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ∧ $r:fnExpr) =>
    pure (.and (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr ∨ $r:fnExpr) =>
    pure (.or (← parseExpr l) (← parseExpr r))
  | `(fnExpr| $l:fnExpr → $r:fnExpr) =>
    pure (.implies (← parseExpr l) (← parseExpr r))
  | `(fnExpr| ∀∀ $p:ident , $b:fnExpr) =>
    pure (.forall_ (toString p.getId) (← parseExpr b))
  | `(fnExpr| sorry) => pure .sorryProof
  | `(fnExpr| lean_proof($s:str)) =>
    pure (.leanProof s.getString)
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
    pure (.match_ scrutAst parsedArms.toList)
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
    : Lean.Elab.Command.CommandElabM
        (String × List String) := do
  match stx with
  | `(fnPrecond| $n:ident ($args:ident,*)) =>
    pure (toString n.getId,
      args.getElems.toList.map
        (toString ·.getId))
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

open Lean Elab Command in
def buildFnDef
    (hdr : FnDefHeader)
    (paramData : Array (Ident × TSyntax `term
      × Syntax))
    (retTy : TSyntax `term)
    (body : TSyntax `term)
    (preconds : List (String × List String) := [])
    (mutualGroup : Option String := none)
    (display : Option (TSyntax `term) := none)
    : CommandElabM Unit := do
  let name := hdr.name
  let symDoc := hdr.symDoc
  let doc := hdr.doc
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
  let precondDefs ← preconds.mapM fun (pn, args) => do
    `({ name := $(quote pn),
        args := $(quote args) : Precondition })
  let precondList ← `([$[$precondDefs.toArray],*])
  let mutualGroupTerm : TSyntax `term := quote mutualGroup
  let displayTerm : TSyntax `term ← match display with
    | some dpList => `((some $dpList : Option (List DisplayPart)))
    | none => `((none : Option (List DisplayPart)))
  let fnDefId := mkIdent (name.getId ++ `fnDef)
  elabCommand (← `(command|
    def $fnDefId : FnDef :=
      { name := $ns,
        symbolDoc := ($symDoc : Doc),
        doc := ($doc : Doc),
        params := $paramList,
        returnType := $retTn,
        preconditions := $precondList,
        body := $body,
        mutualGroup := $mutualGroupTerm,
        display := $displayTerm }))
  let mod ← getMainModule
  let modName : TSyntax `term := quote mod
  elabCommand (← `(command|
    initialize registerFnDef $fnDefId $modName))

/-- Build precondition proof parameter strings for
    the generated Lean def. Each precondition
    `prop(a, b)` becomes `(h_prop : prop a b)`. -/
private def precondParamBinds
    (preconds : List (String × List String))
    : String :=
  " ".intercalate
    (preconds.map fun (pn, args) =>
      let argStr := " ".intercalate args
      s!"(h_{pn} : {pn} {argStr})")

-- ══════════════════════════════════════════════
-- Pattern-matching form
-- ══════════════════════════════════════════════

open Lean Elab Command Term in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam* $[displayed ( $dps:displayPart,* )]?
       $[requires $reqs:fnPrecond,*]?
       : $retTy:term where
       $arms:fnArm*) => do
    identRefBuffer.set #[]
    let paramData ← ps.mapM parseFnParam
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
    -- Generate Lean def via string parsing
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        let rhsStr := rhsAst.toLeanWith
          fnNameStr precondNames
        s!"  | {patStr} => {rhsStr}"
    let defKw := "def"
    let paramNames := paramData.toList.map
      fun (pn, _, _) => toString pn.getId
    let defStr ←
      if preconds.isEmpty then
        let tyStr ← buildFnType paramData retTy
        pure s!"{defKw} {name.getId} : {tyStr}\n\
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
        let retRepr := normaliseLeanType retRaw
        let matchArgs := ", ".intercalate paramNames
        pure s!"{defKw} {name.getId} \
          {paramBinds} {precBinds} : {retRepr} :=\n\
          match {matchArgs} with\n\
          {"\n".intercalate armStrs}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    -- Build FnBody metadata
    let armDefs ← parsed.mapM
      fun (patAst, rhsAst) => do
        let pq : TSyntax `term := quote patAst.toList
        let rq : TSyntax `term := quote rhsAst
        `({ pat := $pq, rhs := $rq : BodyArm })
    let armList ← `([$[$armDefs],*])
    let bodyTerm ← `(FnBody.matchArms $armList)
    buildFnDef ⟨name, symDoc, doc⟩ paramData retTy
      bodyTerm preconds (display := displayTerm)
    flushIdentRefs

-- ══════════════════════════════════════════════
-- Direct expression form
-- ══════════════════════════════════════════════

open Lean Elab Command in
elab_rules : command
  | `(defFn $name:ident ($symDoc:term) ($doc:term)
       $ps:fnParam* $[displayed ( $dps:displayPart,* )]?
       $[requires $reqs:fnPrecond,*]?
       : $retTy:term := $rhs:fnExpr) => do
    identRefBuffer.set #[]
    let paramData ← ps.mapM parseFnParam
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
    let rhsAst ← parseExpr rhs
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let rhsStr := rhsAst.toLeanWith
      fnNameStr precondNames
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
    let retRepr := normaliseLeanType retRaw
    let defStr :=
      s!"def {name.getId} {paramBinds} \
         {precBinds} : {retRepr} :=\n  {rhsStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      defStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFn: parse error: {e}\n\
        ---\n{defStr}\n---"
    let bodyTerm ←
      `(FnBody.expr $(quote rhsAst))
    buildFnDef ⟨name, symDoc, doc⟩ paramData retTy
      bodyTerm preconds (display := displayTerm)
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
  preconds : List (String × List String)
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
          : $retTy:term where
          $arms:fnArm*) => do
    let paramData ← ps.mapM parseFnParam
    for (_, _, ty) in paramData do recordTypeIdents ty
    recordTypeIdents retTy
    let displayTerm ← match dps with
      | some d => Option.some <$> parseFnDisplay paramData d.getElems
      | none => pure none
    let preconds ← match reqs with
      | some pcs =>
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
    let fnNameStr := toString name.getId
    let precondNames := preconds.map (·.1)
    let armStrs := parsed.toList.map
      fun (patAst, rhsAst) =>
        let patStr := ", ".intercalate
          (patAst.toList.map BodyPat.toLean)
        let rhsStr := rhsAst.toLeanWith
          fnNameStr precondNames
        s!"  | {patStr} => {rhsStr}"
    let defStr ←
      if preconds.isEmpty then
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
        let retRepr := normaliseLeanType retRaw
        let paramNames := paramData.toList.map
          fun (pn, _, _) => toString pn.getId
        let matchArgs := ", ".intercalate paramNames
        pure s!"def {name.getId} \
          {paramBinds} {precBinds} : {retRepr} :=\n\
          match {matchArgs} with\n\
          {"\n".intercalate armStrs}"
    pure { defStr, name, symDoc, doc, paramData, retTy,
           preconds, parsed, display := displayTerm }
  | _ => throwError "invalid mutualFnEntry"

open Lean Elab Command Term in
elab_rules : command
  | `(defFnMutual $entries:mutualFnEntry* end) => do
    identRefBuffer.set #[]
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
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defFnMutual: parse error: {e}\n\
        ---\n{mutualStr}\n---"
    -- Tag every entry with a shared group id derived from
    -- the first entry's name, so the Lean backend can emit
    -- them inside a single `mutual … end` block.
    let groupTag ← match results[0]? with
      | some r => pure s!"{r.name.getId}"
      | none => throwError "defFnMutual: expected at least one entry"
    for r in results do
      let armDefs ← r.parsed.mapM
        fun (patAst, rhsAst) => do
          let pq : TSyntax `term := quote patAst.toList
          let rq : TSyntax `term := quote rhsAst
          `({ pat := $pq, rhs := $rq : BodyArm })
      let armList ← `([$[$armDefs],*])
      let bodyTerm ← `(FnBody.matchArms $armList)
      buildFnDef ⟨r.name, r.symDoc, r.doc⟩ r.paramData
        r.retTy bodyTerm r.preconds (mutualGroup := some groupTag)
        (display := r.display)
    flushIdentRefs
