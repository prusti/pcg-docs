import Core.Export.Latex
import Core.Dsl.DeriveQuote
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.BodyPat
import Core.Dsl.DslType
import Core.Meta.BaseFunctor

/-- An expression in the DSL. -/
inductive DslExpr where
  | var (name : String)
  | natLit (n : Nat)
  | true_
  | false_
  | emptyList
  | none_
  | some_ (e : DslExpr)
  /-- Struct constructor. `name` is the struct name
      (empty for anonymous tuples). -/
  | mkStruct (name : String) (args : List DslExpr)
  | cons (head : DslExpr) (tail : DslExpr)
  | append (lhs : DslExpr) (rhs : DslExpr)
  | dot (recv : DslExpr) (method : String)
  | flatMap (list : DslExpr) (param : String)
      (body : DslExpr)
  /-- List map: `list.map fun param => body`. -/
  | map (list : DslExpr) (param : String)
      (body : DslExpr)
  /-- List map with a named function: `list.map fn`. -/
  | mapFn (list : DslExpr) (fn : String)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : DslExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : DslExpr) (idx : DslExpr)
  /-- Infallible list indexing: `list[idx]`. -/
  | indexBang (list : DslExpr) (idx : DslExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : String) (args : List DslExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : String) (init : DslExpr)
      (list : DslExpr)
  /-- Less-than comparison: `lhs < rhs`. -/
  | lt (lhs : DslExpr) (rhs : DslExpr)
  /-- Less-than-or-equal: `lhs ≤ rhs`. -/
  | le (lhs : DslExpr) (rhs : DslExpr)
  /-- Chained less-than: `a < b < c < …`. -/
  | ltChain (exprs : List DslExpr)
  /-- Chained less-than-or-equal: `a ≤ b ≤ c ≤ …`. -/
  | leChain (exprs : List DslExpr)
  /-- Addition: `lhs + rhs`. -/
  | add (lhs : DslExpr) (rhs : DslExpr)
  | sub (lhs : DslExpr) (rhs : DslExpr)
  | mul (lhs : DslExpr) (rhs : DslExpr)
  | div (lhs : DslExpr) (rhs : DslExpr)
  /-- Universal quantifier over a set:
      `∀ x ∈ s, body`. -/
  | setAll (set : DslExpr) (param : String)
      (body : DslExpr)
  /-- Empty set: `∅`. -/
  | emptySet
  /-- Set singleton: `{elem}`. -/
  | setSingleton (elem : DslExpr)
  /-- Set union: `lhs ∪ rhs`. -/
  | setUnion (lhs : DslExpr) (rhs : DslExpr)
  /-- Set flat-map: `⋃_{param ∈ list} body`. -/
  | setFlatMap (list : DslExpr) (param : String)
      (body : DslExpr)
  /-- Logical conjunction: `lhs ∧ rhs`. -/
  | and (lhs : DslExpr) (rhs : DslExpr)
  /-- Logical disjunction: `lhs ∨ rhs`. -/
  | or (lhs : DslExpr) (rhs : DslExpr)
  /-- Implication: `lhs → rhs`. -/
  | implies (lhs : DslExpr) (rhs : DslExpr)
  /-- Universal quantifier: `∀ x, body`. -/
  | forall_ (param : String) (body : DslExpr)
  /-- Proof placeholder: `sorry`. Used when calling
      a function with preconditions from another
      function that can supply the proof. -/
  | sorryProof
  /-- Raw Lean proof term, invisible in Rust/LaTeX. -/
  | leanProof (term : String)
  /-- Match expression:
      `match scrutinee with | pats => rhs | …`.
      Each arm is a list of patterns paired with a
      right-hand side. -/
  | match_ (scrutinee : DslExpr)
      (arms : List (List BodyPat × DslExpr))
  /-- `let name := val ; body`. -/
  | letIn (name : String) (val : DslExpr) (body : DslExpr)
  /-- `let name ← val ; body` (monadic bind on Option). -/
  | letBindIn (name : String) (val : DslExpr) (body : DslExpr)
  /-- `if cond then t else e`. -/
  | ifThenElse (cond : DslExpr) (t : DslExpr) (e : DslExpr)
  /-- Inequality: `lhs ≠ rhs`. -/
  | neq (lhs : DslExpr) (rhs : DslExpr)
  deriving Repr, Inhabited, Lean.Quote

-- Generate `DslExprF`, `project`, `embed`, `map`, `mapM`, `cata`, `cataM`,
-- `para`, `paraM`. See `Core.Meta.BaseFunctor` for details.
derive_base_functor DslExpr

namespace DslExpr

/-- Apply `f` to every immediate `DslExpr` child of a
    node, leaving non-`DslExpr` fields unchanged. -/
def mapChildren (f : DslExpr → DslExpr)
    : DslExpr → DslExpr
  -- Leaves (no DslExpr children)
  | .var n => .var n
  | .natLit n => .natLit n
  | .true_ => .true_
  | .false_ => .false_
  | .emptyList => .emptyList
  | .none_ => .none_
  | .emptySet => .emptySet
  | .sorryProof => .sorryProof
  | .leanProof t => .leanProof t
  -- Unary
  | .some_ e => .some_ (f e)
  | .dot e m => .dot (f e) m
  | .field e n => .field (f e) n
  | .setSingleton e => .setSingleton (f e)
  | .forall_ p b => .forall_ p (f b)
  | .mapFn l fn => .mapFn (f l) fn
  -- Binary
  | .cons h t => .cons (f h) (f t)
  | .append l r => .append (f l) (f r)
  | .index l i => .index (f l) (f i)
  | .indexBang l i => .indexBang (f l) (f i)
  | .lt l r => .lt (f l) (f r)
  | .le l r => .le (f l) (f r)
  | .add l r => .add (f l) (f r)
  | .sub l r => .sub (f l) (f r)
  | .mul l r => .mul (f l) (f r)
  | .div l r => .div (f l) (f r)
  | .setUnion l r => .setUnion (f l) (f r)
  | .and l r => .and (f l) (f r)
  | .or l r => .or (f l) (f r)
  | .implies l r => .implies (f l) (f r)
  | .neq l r => .neq (f l) (f r)
  -- Ternary (with String parameter)
  | .flatMap l p b => .flatMap (f l) p (f b)
  | .map l p b => .map (f l) p (f b)
  | .setAll s p b => .setAll (f s) p (f b)
  | .setFlatMap l p b => .setFlatMap (f l) p (f b)
  | .letIn n v b => .letIn n (f v) (f b)
  | .letBindIn n v b => .letBindIn n (f v) (f b)
  | .ifThenElse c t e => .ifThenElse (f c) (f t) (f e)
  | .foldlM fn init list => .foldlM fn (f init) (f list)
  -- List children
  | .mkStruct n args => .mkStruct n (args.map f)
  | .call fn args => .call fn (args.map f)
  | .ltChain es => .ltChain (es.map f)
  | .leChain es => .leChain (es.map f)
  -- Match (recurse into scrutinee and arm RHSs)
  | .match_ s arms =>
    .match_ (f s) (arms.map fun (p, rhs) => (p, f rhs))

/-- Bottom-up rewrite: recurse into all children first,
    then apply `f` to the rebuilt node. Equivalent to
    `transform` from Haskell's `uniplate` library. -/
partial def transform
    (f : DslExpr → DslExpr) (e : DslExpr)
    : DslExpr :=
  f (e.mapChildren (transform f))

end DslExpr

-- ══════════════════════════════════════════════
-- Doc rendering
-- ══════════════════════════════════════════════

/-- Embed verbatim LaTeX math content into a `MathDoc`.

    This should be avoided as much as possible: the input string
    is LaTeX-specific, bypasses all escaping, and does not render
    sensibly in non-LaTeX backends (HTML, plain text). Prefer a
    structured `MathDoc`/`MathSym` constructor, or extend them
    with a new variant when none fits. This function is only
    retained for genuinely raw-LaTeX constructs (e.g.
    `\hyperlink{…}`, `\begin{array}`) that have no
    backend-independent representation yet. -/
private def rawMath (s : String) : MathDoc :=
  .doc (.raw s "" "")

namespace DslExpr

partial def toDoc
    (fnName : String)
    (varDisplay : String → Option MathDoc :=
      fun _ => none)
    (ctorDisplay : String → Option MathDoc :=
      fun _ => none)
    (isProperty : Bool := false)
    (knownFns : String → Bool := fun _ => false)
    (resolveCtor : String → Option String := fun _ => none)
    (knownTypes : String → Bool := fun _ => false)
    : DslExpr → MathDoc :=
  let go := toDoc fnName varDisplay ctorDisplay
    isProperty knownFns resolveCtor knownTypes
  let ctorRef := BodyPat.ctorRef resolveCtor
  -- Link a struct constructor to its type definition. Falls
  -- back to `ctorRef` so that enum-variant constructors remain
  -- linked to their ctor target.
  let structRef (n : String) : MathDoc :=
    if knownTypes n then
      .doc (.link (.underline .dashed (.plain n))
        s!"#type:{n}")
    else ctorRef n
  let fnRef (fn : String) : MathDoc :=
    -- Strip any namespace prefix (e.g. `Memory.store` →
    -- `store`) so qualified calls still resolve to the
    -- labelled function. Fall back to a constructor
    -- reference (e.g. `Value.int`) when the name does
    -- not match a known function.
    let shortName := (fn.splitOn ".").getLast?.getD fn
    if knownFns shortName then
      .doc (.link (.underline .dashed (.plain fn))
        s!"#fn:{shortName}")
    else ctorRef fn
  -- A trailing keyword like `let ` / `if ` / `match ` with
  -- a non-breaking space after the word.
  let keyword (s : String) : MathDoc :=
    .seq [MathDoc.text s, .sym .space]
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none => .raw n
  | .natLit n => .raw (toString n)
  | .true_ =>
    if isProperty then .sym .top
    else MathDoc.text "true"
  | .false_ =>
    if isProperty then .sym .bot
    else MathDoc.text "false"
  | .emptyList => MathDoc.bracket (.seq [])
  | .none_ => MathDoc.text "None"
  | .some_ e =>
    .seq [MathDoc.text "Some", MathDoc.paren (go e)]
  | .mkStruct name args =>
    let argList : MathDoc :=
      MathDoc.paren
        (mathIntercalate (.sym .comma) (args.map go))
    if name == "" then argList
    else .seq [structRef name, argList]
  | .cons h t =>
    -- Flatten cons chains ending in `emptyList` into a
    -- list literal `[e₁, e₂, …]`.
    let rec flatten : DslExpr → Option (List DslExpr)
      | .emptyList => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      MathDoc.bracket
        (mathIntercalate (.sym .comma) (elems.map go))
    | none => .seq [go h, .sym .cons, go t]
  | .append l r => .seq [go l, .sym .append, go r]
  | .dot recv "length" =>
    .seq [.sym .pipe, go recv, .sym .pipe]
  | .dot recv "toNat" =>
    .seq [ go recv, .sym .space, MathDoc.text "as"
         , .sym .space, .bb (.raw "N") ]
  | .dot recv method =>
    .seq [fnRef method, MathDoc.paren (go recv)]
  | .flatMap list param body =>
    .seq [ go list, .sym .dot, MathDoc.text "flatMap"
         , MathDoc.paren (.seq
             [ .sym .lambda, .raw param, .sym .dot
             , .sym .space, go body ]) ]
  | .map list param body =>
    .seq [ go list, .sym .dot, MathDoc.text "map"
         , MathDoc.paren (.seq
             [ .sym .lambda, .raw param, .sym .dot
             , .sym .space, go body ]) ]
  | .mapFn list fn =>
    .seq [ go list, .sym .dot, MathDoc.text "map"
         , MathDoc.paren (fnRef fn) ]
  | .field recv name =>
    .seq [go recv, .sym .dot, MathDoc.text name]
  | .index list idx =>
    .seq [go list, MathDoc.bracket (go idx)]
  | .indexBang list idx =>
    .seq [go list, MathDoc.bracket (go idx)]
  | .call "listSet" [a, b, c] =>
    .seq [ go a, MathDoc.bracket
             (.seq [go b, .sym .mapsto, go c]) ]
  | .call "mapGet" [a, b] =>
    .seq [go a, MathDoc.bracket (go b)]
  | .call fn args =>
    -- Drop proof arguments: they render as empty math
    -- and would otherwise leave a trailing comma.
    let visibleArgs := args.filter fun
      | .sorryProof => false
      | .leanProof _ => false
      | _ => true
    .seq [ fnRef fn, MathDoc.paren
             (mathIntercalate (.sym .comma)
               (visibleArgs.map go)) ]
  | .foldlM fn init list =>
    -- `^*` is a superscript that decorates the function
    -- reference; no backend-independent form yet.
    .seq [ fnRef fn, rawMath "^*"
         , MathDoc.paren
             (.seq [go init, .sym .comma, go list]) ]
  | .lt l r => .seq [go l, .sym .lt, go r]
  | .le l r => .seq [go l, .sym .le, go r]
  | .ltChain es => mathIntercalate (.sym .lt) (es.map go)
  | .leChain es => mathIntercalate (.sym .le) (es.map go)
  | .add l r => .seq [go l, .sym .add, go r]
  | .sub l r => .seq [go l, .sym .sub, go r]
  | .mul l r => .seq [go l, .sym .mul, go r]
  | .div l r => .seq [go l, .sym .div, go r]
  | .setAll set param body =>
    .seq [ .sym .forall_, .raw param
         , .sym .setContains, go set
         , .sym .comma, go body ]
  | .emptySet => .sym .emptySet
  | .setSingleton e => MathDoc.brace (go e)
  | .setUnion l r => .seq [go l, .sym .cup, go r]
  | .setFlatMap list param body =>
    -- `\bigcup_{…}` is a LaTeX-specific big operator with
    -- subscript; no backend-independent form yet.
    .seq [ rawMath "\\bigcup_{", .raw param
         , .sym .setContains, go list, rawMath "} "
         , go body ]
  | .and l r => .seq [go l, .sym .land, go r]
  | .or l r => .seq [go l, .sym .lor, go r]
  | .implies l r => .seq [go l, .sym .implies, go r]
  | .forall_ p b =>
    .seq [.sym .forall_, .raw p, .sym .comma, go b]
  | .sorryProof => .seq []
  | .leanProof _ => .seq []
  | .match_ scrut arms =>
    let noCtor : String → Option MathDoc :=
      fun _ => Option.none
    let rowsMath : List MathDoc :=
      arms.map fun (pats, rhs) =>
        let patMath := mathIntercalate (.sym .comma)
          (pats.map (BodyPat.toDoc noCtor))
        -- `&` is the LaTeX array column separator; the
        -- trailing ` \\` ends the array row. These are
        -- LaTeX-specific and stay raw.
        .seq [ rawMath "  ", go rhs
             , rawMath " &", keyword "if", patMath
             , rawMath " \\\\" ]
    -- `\left\{\begin{array}{ll}…\end{array}\right.` is a
    -- LaTeX-specific aligned-cases environment; kept raw.
    .seq [ keyword "match", go scrut
         , rawMath ": \\left\\{\\begin{array}{ll}\n"
         , mathIntercalate (rawMath "\n") rowsMath
         , rawMath "\n\\end{array}\\right." ]
  | .letIn name val body =>
    .seq [ keyword "let", .raw name, .sym .assign
         , go val, .sym .semicolon, .sym .space, go body ]
  | .letBindIn name val body =>
    .seq [ keyword "let", .raw name, .sym .leftarrow
         , go val, .sym .semicolon, .sym .space, go body ]
  | .ifThenElse c t e =>
    .seq [ keyword "if", go c, .sym .space
         , keyword "then", go t, .sym .space
         , keyword "else", go e ]
  | .neq l r => .seq [go l, .sym .neq, go r]

end DslExpr
