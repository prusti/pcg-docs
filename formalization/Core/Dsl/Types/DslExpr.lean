import Core.Export.Latex
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.DslType

/-- A pattern in a function body. -/
inductive BodyPat where
  | wild
  | var (name : String)
  | ctor (name : String) (args : List BodyPat)
  /-- Empty list pattern: `[]`. -/
  | nil
  /-- List cons pattern: `h :: t`. -/
  | cons (head : BodyPat) (tail : BodyPat)
  /-- Numeric literal pattern. -/
  | natLit (n : Nat)
  deriving Repr, Inhabited

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
  /-- Addition: `lhs + rhs`. -/
  | add (lhs : DslExpr) (rhs : DslExpr)
  | sub (lhs : DslExpr) (rhs : DslExpr)
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
  deriving Repr, Inhabited

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
-- Quote instances
-- ══════════════════════════════════════════════

open Lean in
partial def quotePat : BodyPat → TSyntax `term
  | .wild => Syntax.mkApp (mkIdent ``BodyPat.wild) #[]
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyPat.var) #[quote n]
  | .ctor n args =>
    let qArgs := args.map quotePat
    Syntax.mkApp (mkIdent ``BodyPat.ctor)
      #[quote n, quote qArgs]
  | .nil =>
    Syntax.mkApp (mkIdent ``BodyPat.nil) #[]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyPat.cons)
      #[quotePat h, quotePat t]
  | .natLit n =>
    Syntax.mkApp (mkIdent ``BodyPat.natLit) #[quote n]

open Lean in
instance : Quote BodyPat where quote := quotePat

open Lean in
partial def quoteExpr : DslExpr → TSyntax `term
  | .var n =>
    Syntax.mkApp (mkIdent ``DslExpr.var) #[quote n]
  | .natLit n =>
    Syntax.mkApp (mkIdent ``DslExpr.natLit) #[quote n]
  | .true_ =>
    Syntax.mkApp (mkIdent ``DslExpr.true_) #[]
  | .false_ =>
    Syntax.mkApp (mkIdent ``DslExpr.false_) #[]
  | .emptyList =>
    Syntax.mkApp (mkIdent ``DslExpr.emptyList) #[]
  | .none_ =>
    Syntax.mkApp (mkIdent ``DslExpr.none_) #[]
  | .some_ e =>
    Syntax.mkApp (mkIdent ``DslExpr.some_)
      #[quoteExpr e]
  | .mkStruct name args =>
    Syntax.mkApp (mkIdent ``DslExpr.mkStruct)
      #[quote name, quote (args.map quoteExpr)]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``DslExpr.cons)
      #[quoteExpr h, quoteExpr t]
  | .append l r =>
    Syntax.mkApp (mkIdent ``DslExpr.append)
      #[quoteExpr l, quoteExpr r]
  | .dot recv method =>
    Syntax.mkApp (mkIdent ``DslExpr.dot)
      #[quoteExpr recv, quote method]
  | .flatMap list param body =>
    Syntax.mkApp (mkIdent ``DslExpr.flatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .map list param body =>
    Syntax.mkApp (mkIdent ``DslExpr.map)
      #[quoteExpr list, quote param, quoteExpr body]
  | .mapFn list fn =>
    Syntax.mkApp (mkIdent ``DslExpr.mapFn)
      #[quoteExpr list, quote fn]
  | .field recv name =>
    Syntax.mkApp (mkIdent ``DslExpr.field)
      #[quoteExpr recv, quote name]
  | .index list idx =>
    Syntax.mkApp (mkIdent ``DslExpr.index)
      #[quoteExpr list, quoteExpr idx]
  | .indexBang list idx =>
    Syntax.mkApp (mkIdent ``DslExpr.indexBang)
      #[quoteExpr list, quoteExpr idx]
  | .call fn args =>
    Syntax.mkApp (mkIdent ``DslExpr.call)
      #[quote fn, quote (args.map quoteExpr)]
  | .foldlM fn init list =>
    Syntax.mkApp (mkIdent ``DslExpr.foldlM)
      #[quote fn, quoteExpr init, quoteExpr list]
  | .lt l r =>
    Syntax.mkApp (mkIdent ``DslExpr.lt)
      #[quoteExpr l, quoteExpr r]
  | .le l r =>
    Syntax.mkApp (mkIdent ``DslExpr.le)
      #[quoteExpr l, quoteExpr r]
  | .ltChain es =>
    Syntax.mkApp (mkIdent ``DslExpr.ltChain)
      #[quote (es.map quoteExpr)]
  | .add l r =>
    Syntax.mkApp (mkIdent ``DslExpr.add)
      #[quoteExpr l, quoteExpr r]
  | .sub l r =>
    Syntax.mkApp (mkIdent ``DslExpr.sub)
      #[quoteExpr l, quoteExpr r]
  | .div l r =>
    Syntax.mkApp (mkIdent ``DslExpr.div)
      #[quoteExpr l, quoteExpr r]
  | .setAll set param body =>
    Syntax.mkApp (mkIdent ``DslExpr.setAll)
      #[quoteExpr set, quote param, quoteExpr body]
  | .emptySet =>
    Syntax.mkApp (mkIdent ``DslExpr.emptySet) #[]
  | .setSingleton e =>
    Syntax.mkApp (mkIdent ``DslExpr.setSingleton)
      #[quoteExpr e]
  | .setUnion l r =>
    Syntax.mkApp (mkIdent ``DslExpr.setUnion)
      #[quoteExpr l, quoteExpr r]
  | .setFlatMap list param body =>
    Syntax.mkApp (mkIdent ``DslExpr.setFlatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .and l r =>
    Syntax.mkApp (mkIdent ``DslExpr.and)
      #[quoteExpr l, quoteExpr r]
  | .or l r =>
    Syntax.mkApp (mkIdent ``DslExpr.or)
      #[quoteExpr l, quoteExpr r]
  | .implies l r =>
    Syntax.mkApp (mkIdent ``DslExpr.implies)
      #[quoteExpr l, quoteExpr r]
  | .forall_ p b =>
    Syntax.mkApp (mkIdent ``DslExpr.forall_)
      #[quote p, quoteExpr b]
  | .sorryProof =>
    Syntax.mkApp (mkIdent ``DslExpr.sorryProof) #[]
  | .leanProof t =>
    Syntax.mkApp (mkIdent ``DslExpr.leanProof) #[quote t]
  | .match_ scrut arms =>
    let qArms := arms.map fun (pats, rhs) =>
      Syntax.mkApp (mkIdent ``Prod.mk)
        #[quote pats, quoteExpr rhs]
    Syntax.mkApp (mkIdent ``DslExpr.match_)
      #[quoteExpr scrut, quote qArms]
  | .letIn name val body =>
    Syntax.mkApp (mkIdent ``DslExpr.letIn)
      #[quote name, quoteExpr val, quoteExpr body]
  | .letBindIn name val body =>
    Syntax.mkApp (mkIdent ``DslExpr.letBindIn)
      #[quote name, quoteExpr val, quoteExpr body]
  | .ifThenElse c t e =>
    Syntax.mkApp (mkIdent ``DslExpr.ifThenElse)
      #[quoteExpr c, quoteExpr t, quoteExpr e]
  | .neq l r =>
    Syntax.mkApp (mkIdent ``DslExpr.neq)
      #[quoteExpr l, quoteExpr r]

open Lean in
instance : Quote DslExpr where quote := quoteExpr

-- ══════════════════════════════════════════════
-- Doc rendering
-- ══════════════════════════════════════════════

/-- Embed verbatim LaTeX math content into a `MathDoc`. -/
private def rawMath (s : String) : MathDoc :=
  .doc (.raw s "" "")

/-- Intercalate a separator between math doc fragments. -/
private def mathIntercalate (sep : MathDoc)
    : List MathDoc → MathDoc
  | [] => .seq []
  | [m] => m
  | ms => .seq (ms.intersperse sep)

namespace BodyPat

/-- Render a constructor name as a hyperlinked `\dashuline`
    reference when it matches a known variant. Accepts
    either short (`int`) or qualified (`Value.int`) forms;
    the label uses the short name. -/
private def ctorRef
    (knownCtors : String → Bool) (n : String) : MathDoc :=
  let shortName := (n.splitOn ".").getLast?.getD n
  if knownCtors shortName then
    rawMath s!"\\text\{\\hyperlink\{ctor:{shortName}}\
               \{\\dashuline\{{n}}}}"
  else rawMath s!"\\text\{{n}}"

partial def toDoc
    (ctorDisplay : String → Option MathDoc)
    (knownCtors : String → Bool := fun _ => false)
    : BodyPat → MathDoc
  | .wild => rawMath "\\_"
  | .var n => .raw n
  | .ctor "⟨⟩" args =>
    .seq [ rawMath "("
         , mathIntercalate (rawMath ",~")
             (args.map (toDoc ctorDisplay knownCtors))
         , rawMath ")" ]
  | .ctor n args =>
    if args.isEmpty then
      match ctorDisplay n with
      | some display => display
      | none => ctorRef knownCtors n
    else
      let argParts :=
        args.map (toDoc ctorDisplay knownCtors)
      .seq [ ctorRef knownCtors n, rawMath "("
           , mathIntercalate (rawMath ",~") argParts
           , rawMath ")" ]
  | .nil => rawMath "[]"
  | .cons h t =>
    let rec flatten : BodyPat → Option (List BodyPat)
      | .nil => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      .seq [ rawMath "["
           , mathIntercalate (rawMath ",~")
               (elems.map
                 (toDoc ctorDisplay knownCtors))
           , rawMath "]" ]
    | none =>
      .seq [ h.toDoc ctorDisplay knownCtors
           , rawMath " :: "
           , t.toDoc ctorDisplay knownCtors ]
  | .natLit n => rawMath (toString n)

end BodyPat

namespace DslExpr

partial def toDoc
    (fnName : String)
    (varDisplay : String → Option MathDoc :=
      fun _ => none)
    (ctorDisplay : String → Option MathDoc :=
      fun _ => none)
    (isProperty : Bool := false)
    (knownFns : String → Bool := fun _ => false)
    (knownCtors : String → Bool := fun _ => false)
    (knownTypes : String → Bool := fun _ => false)
    : DslExpr → MathDoc :=
  let go := toDoc fnName varDisplay ctorDisplay
    isProperty knownFns knownCtors knownTypes
  let ctorRef := BodyPat.ctorRef knownCtors
  -- Link a struct constructor to its type definition via
  -- `\hyperlink{type:<name>}`. Falls back to `ctorRef` so
  -- that enum-variant constructors remain linked to their
  -- ctor target.
  let structRef (n : String) : MathDoc :=
    if knownTypes n then
      rawMath s!"\\text\{\\hyperlink\{type:{n}}\
                 \{\\dashuline\{{n}}}}"
    else ctorRef n
  let fnRef (fn : String) : MathDoc :=
    -- Strip any namespace prefix (e.g. `Memory.store` →
    -- `store`) so qualified calls still resolve to the
    -- labelled function. Fall back to a constructor
    -- reference (e.g. `Value.int`) when the name does
    -- not match a known function.
    let shortName := (fn.splitOn ".").getLast?.getD fn
    if knownFns shortName then
      rawMath s!"\\text\{\\hyperref[fn:{shortName}]\
                 \{\\dashuline\{{fn}}}}"
    else ctorRef fn
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none => .raw n
  | .natLit n => rawMath (toString n)
  | .true_ =>
    if isProperty then rawMath "\\top"
    else rawMath "\\text{true}"
  | .false_ =>
    if isProperty then rawMath "\\bot"
    else rawMath "\\text{false}"
  | .emptyList => rawMath "[]"
  | .none_ => rawMath "\\text{None}"
  | .some_ e =>
    .seq [ rawMath "\\text{Some}", rawMath "("
         , go e, rawMath ")" ]
  | .mkStruct name args =>
    if name == "" then
      .seq [ rawMath "("
           , mathIntercalate (rawMath ",~")
               (args.map go)
           , rawMath ")" ]
    else
      .seq [ structRef name, rawMath "("
           , mathIntercalate (rawMath ",~")
               (args.map go)
           , rawMath ")" ]
  | .cons h t =>
    -- Flatten cons chains ending in `emptyList` into a
    -- list literal `[e₁, e₂, …]`.
    let rec flatten : DslExpr → Option (List DslExpr)
      | .emptyList => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      .seq [ rawMath "["
           , mathIntercalate (rawMath ",~")
               (elems.map go)
           , rawMath "]" ]
    | none => .seq [go h, rawMath " :: ", go t]
  | .append l r =>
    .seq [ go l, rawMath " \\mathbin{\\texttt{++}} "
         , go r ]
  | .dot recv "length" =>
    .seq [rawMath "|", go recv, rawMath "|"]
  | .dot recv "toNat" =>
    .seq [go recv, rawMath "~\\text{as}~",
          .bb (rawMath "N")]
  | .dot recv method =>
    .seq [fnRef method, rawMath "(", go recv,
          rawMath ")"]
  | .flatMap list param body =>
    .seq [ go list, rawMath ".\\text{flatMap}(\\lambda "
         , .raw param, rawMath ".~", go body
         , rawMath ")" ]
  | .map list param body =>
    .seq [ go list, rawMath ".\\text{map}(\\lambda "
         , .raw param, rawMath ".~", go body
         , rawMath ")" ]
  | .mapFn list fn =>
    .seq [ go list, rawMath ".\\text{map}("
         , fnRef fn, rawMath ")" ]
  | .field recv name =>
    .seq [go recv, rawMath ".",
          rawMath s!"\\text\{{name}}"]
  | .index list idx =>
    .seq [go list, rawMath "[", go idx, rawMath "]"]
  | .indexBang list idx =>
    .seq [go list, rawMath "[", go idx, rawMath "]"]
  | .call "listSet" [a, b, c] =>
    .seq [ go a, rawMath "[", go b, rawMath " \\mapsto "
         , go c, rawMath "]" ]
  | .call "mapGet" [a, b] =>
    .seq [ go a, rawMath "[", go b, rawMath "]" ]
  | .call fn args =>
    -- Drop proof arguments: they render as empty math
    -- and would otherwise leave a trailing comma.
    let visibleArgs := args.filter fun
      | .sorryProof => false
      | .leanProof _ => false
      | _ => true
    .seq [ fnRef fn, rawMath "("
         , mathIntercalate (rawMath ",~")
             (visibleArgs.map go)
         , rawMath ")" ]
  | .foldlM fn init list =>
    .seq [ fnRef fn, rawMath "^*(", go init
         , rawMath ",~", go list, rawMath ")" ]
  | .lt l r => .seq [go l, rawMath " < ", go r]
  | .le l r => .seq [go l, rawMath " \\leqslant ", go r]
  | .ltChain es =>
    mathIntercalate (rawMath " < ") (es.map go)
  | .add l r => .seq [go l, rawMath " + ", go r]
  | .sub l r => .seq [go l, rawMath " - ", go r]
  | .div l r => .seq [go l, rawMath " / ", go r]
  | .setAll set param body =>
    .seq [ rawMath "\\forall ", .raw param
         , rawMath " \\in ", go set
         , rawMath ",~", go body ]
  | .emptySet => rawMath "\\emptyset"
  | .setSingleton e =>
    .seq [rawMath "\\{", go e, rawMath "\\}"]
  | .setUnion l r =>
    .seq [go l, rawMath " \\cup ", go r]
  | .setFlatMap list param body =>
    .seq [ rawMath "\\bigcup_{", .raw param
         , rawMath " \\in ", go list, rawMath "} "
         , go body ]
  | .and l r => .seq [go l, rawMath " \\land ", go r]
  | .or l r => .seq [go l, rawMath " \\lor ", go r]
  | .implies l r => .seq [go l, rawMath " \\to ", go r]
  | .forall_ p b =>
    .seq [ rawMath "\\forall ", .raw p
         , rawMath ",~", go b ]
  | .sorryProof => .seq []
  | .leanProof _ => .seq []
  | .match_ scrut arms =>
    let noCtor : String → Option MathDoc :=
      fun _ => Option.none
    let rowsMath : List MathDoc :=
      arms.map fun (pats, rhs) =>
        let patMath := mathIntercalate (rawMath ",~")
          (pats.map (BodyPat.toDoc noCtor))
        .seq [ rawMath "  ", go rhs
             , rawMath " &\\text{if~}", patMath
             , rawMath " \\\\" ]
    .seq [ rawMath "\\text{match~}"
         , go scrut
         , rawMath ": \\left\\{\\begin{array}{ll}\n"
         , mathIntercalate (rawMath "\n") rowsMath
         , rawMath "\n\\end{array}\\right." ]
  | .letIn name val body =>
    .seq [ rawMath "\\text{let~}", .raw name
         , rawMath " := ", go val, rawMath ";~"
         , go body ]
  | .letBindIn name val body =>
    .seq [ rawMath "\\text{let~}", .raw name
         , rawMath " \\leftarrow "
         , go val, rawMath ";~", go body ]
  | .ifThenElse c t e =>
    .seq [ rawMath "\\text{if~}", go c
         , rawMath "~\\text{then~}", go t
         , rawMath "~\\text{else~}", go e ]
  | .neq l r => .seq [go l, rawMath " \\neq ", go r]

end DslExpr
