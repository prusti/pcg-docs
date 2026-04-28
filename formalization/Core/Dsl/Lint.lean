import Core.Dsl.Types.DslExpr
import Core.Dsl.Types.FnDef

/-! # DSL linter

A small, syntactic linter for `defFn` bodies. The linter walks a
`DslExpr` and reports stylistic / structural problems that the type
system does not catch.

Today the only rule is `irrefutableMatch`: a `match` whose scrutinee
can only succeed against the listed arms (every arm pattern is
irrefutable) is just a destructuring binder dressed up as a match
expression, and should be expressed as a `let` instead. The
canonical example is matching on a `defStruct` value (which has a
single constructor) using an anonymous-tuple pattern. -/

namespace BodyPat

/-- Variable-position names that the DSL parser stores as
    `BodyPat.var` but Lean interprets as nullary constructors.
    These patterns must be treated as refutable so that
    `match b with | true => … | false => …` is not flagged as
    "every arm is irrefutable". -/
private def constructorLikeVarNames : List String :=
  ["true", "false"]

mutual
/-- Whether `p` matches every value of its scrutinee's type.

    Wildcards and most bare variables always match. Anonymous-
    tuple patterns (`⟨a, b, …⟩`) match every tuple iff their
    sub-patterns are themselves all irrefutable. Variable-shaped
    patterns whose name is in `constructorLikeVarNames`
    (currently `true` / `false`) are treated as refutable, since
    Lean resolves them to `Bool` constructors. Every other shape
    (named constructors, list cons / nil, numeric literals) can
    fail. -/
def isIrrefutable : BodyPat → Bool
  | .wild => true
  | .var n => !constructorLikeVarNames.contains n
  | .ctor "⟨⟩" args => allIrrefutable args
  | _ => false

/-- Helper for `isIrrefutable`: walks a pattern list explicitly so
    structural termination (via `BodyPat.rec`) stays visible to
    Lean. `List.all` would obscure it. -/
private def allIrrefutable : List BodyPat → Bool
  | [] => true
  | p :: rest => p.isIrrefutable && allIrrefutable rest
end

end BodyPat

namespace DslLint

/-- A single lint diagnostic. -/
structure Diagnostic where
  /-- Name of the lint rule that fired. -/
  rule : String
  /-- Human-readable message. -/
  message : String
  deriving Repr

/-- Diagnostic message used when `match` is used as a destructuring
    binder. Kept as a single source of truth for the test suite. -/
def irrefutableMatchMessage : String :=
  "match expression has only irrefutable patterns; \
   use a destructuring `let pat := … ; …` instead"

/-- Diagnostic message used when a `defFn` / `defProperty`
    `where`-clause has only irrefutable arm patterns: no case
    analysis is happening, so the body should be a direct
    expression instead of a multi-arm match. -/
def irrefutableWhereMessage : String :=
  "all `where` arms have only irrefutable patterns; \
   use the direct expression form (`:= …`) instead, \
   since no case analysis is being performed"

/-- True iff every arm of the match has only irrefutable patterns —
    that is, the scrutinee is bound rather than analysed. An empty
    arm list is treated as refutable since the parser already
    guarantees `match` arms are non-empty. -/
def matchIsIrrefutable
    (arms : List (List BodyPat × DslExpr)) : Bool :=
  !arms.isEmpty &&
    arms.all fun (pats, _) => pats.all BodyPat.isIrrefutable

/-- Recursive children of a `DslExpr` node, in left-to-right
    order. Mirrors the structure-preserving `mapChildren` but
    extracts children flatly rather than rebuilding the node. -/
private def directChildren : DslExpr → List DslExpr
  | .var _ | .natLit _ | .true_ | .false_ | .emptyList
  | .none_ | .emptySet | .sorryProof | .leanProof _ => []
  | .some_ e | .dot e _ | .field e _ | .setSingleton e
  | .forall_ _ e | .lambda _ e => [e]
  | .cons l r | .append l r | .flatMap l r | .map l r
  | .index l r | .indexBang l r | .lt l r | .le l r
  | .add l r | .sub l r | .mul l r | .div l r
  | .setUnion l r | .and l r | .or l r | .implies l r
  | .neq l r | .eq l r | .propEq l r | .memberOf l r => [l, r]
  | .anyList l _ b | .setAll l _ b | .setFlatMap l _ b
  | .letIn _ l b | .letBindIn _ l b => [l, b]
  | .ifThenElse c t e => [c, t, e]
  | .foldlM fn init list => [fn, init, list]
  | .mkStruct _ args => args
  | .call fn args => fn :: args
  | .ineqChain _ es => es
  | .match_ s arms => s :: arms.map (·.2)
  | .structUpdate r _ v => [r, v]

/-- Lint diagnostics for `e` and every sub-expression. -/
partial def lintExpr (e : DslExpr) : List Diagnostic :=
  let here : List Diagnostic :=
    match e with
    | .match_ _ arms =>
      if matchIsIrrefutable arms then
        [{ rule := "irrefutableMatch",
           message := irrefutableMatchMessage }]
      else []
    | _ => []
  here ++ (directChildren e).flatMap lintExpr

/-- Lint diagnostics for a function body. -/
def lintFnBody : FnBody → List Diagnostic
  | .matchArms arms => arms.flatMap fun a => lintExpr a.rhs
  | .expr e => lintExpr e

/-- Lint diagnostics for a complete function definition. -/
def lintFnDef (f : FnDef) : List Diagnostic :=
  lintFnBody f.body

end DslLint
