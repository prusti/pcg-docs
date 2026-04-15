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

/-- An expression in the function body DSL. -/
inductive BodyExpr where
  | var (name : String)
  | natLit (n : Nat)
  | true_
  | false_
  | emptyList
  | none_
  | some_ (e : BodyExpr)
  /-- Struct constructor. `name` is the struct name
      (empty for anonymous tuples). -/
  | mkStruct (name : String) (args : List BodyExpr)
  | cons (head : BodyExpr) (tail : BodyExpr)
  | append (lhs : BodyExpr) (rhs : BodyExpr)
  | dot (recv : BodyExpr) (method : String)
  | flatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- List map: `list.map fun param => body`. -/
  | map (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- List map with a named function: `list.map fn`. -/
  | mapFn (list : BodyExpr) (fn : String)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : BodyExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : BodyExpr) (idx : BodyExpr)
  /-- Infallible list indexing: `list[idx]`. -/
  | indexBang (list : BodyExpr) (idx : BodyExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : String) (args : List BodyExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : String) (init : BodyExpr)
      (list : BodyExpr)
  /-- Less-than comparison: `lhs < rhs`. -/
  | lt (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Less-than-or-equal: `lhs ≤ rhs`. -/
  | le (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Chained less-than: `a < b < c < …`. -/
  | ltChain (exprs : List BodyExpr)
  /-- Addition: `lhs + rhs`. -/
  | add (lhs : BodyExpr) (rhs : BodyExpr)
  | sub (lhs : BodyExpr) (rhs : BodyExpr)
  | div (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Universal quantifier over a set:
      `∀ x ∈ s, body`. -/
  | setAll (set : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Empty set: `∅`. -/
  | emptySet
  /-- Set singleton: `{elem}`. -/
  | setSingleton (elem : BodyExpr)
  /-- Set union: `lhs ∪ rhs`. -/
  | setUnion (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Set flat-map: `⋃_{param ∈ list} body`. -/
  | setFlatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Logical conjunction: `lhs ∧ rhs`. -/
  | and (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Logical disjunction: `lhs ∨ rhs`. -/
  | or (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Implication: `lhs → rhs`. -/
  | implies (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Universal quantifier: `∀ x, body`. -/
  | forall_ (param : String) (body : BodyExpr)
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
  | match_ (scrutinee : BodyExpr)
      (arms : List (List BodyPat × BodyExpr))
  /-- `let name := val ; body`. -/
  | letIn (name : String) (val : BodyExpr) (body : BodyExpr)
  /-- `let name ← val ; body` (monadic bind on Option). -/
  | letBindIn (name : String) (val : BodyExpr) (body : BodyExpr)
  /-- `if cond then t else e`. -/
  | ifThenElse (cond : BodyExpr) (t : BodyExpr) (e : BodyExpr)
  /-- Inequality: `lhs ≠ rhs`. -/
  | neq (lhs : BodyExpr) (rhs : BodyExpr)
  deriving Repr, Inhabited

namespace BodyExpr

/-- Apply `f` to every immediate `BodyExpr` child of a
    node, leaving non-`BodyExpr` fields unchanged. -/
def mapChildren (f : BodyExpr → BodyExpr)
    : BodyExpr → BodyExpr
  -- Leaves (no BodyExpr children)
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
    (f : BodyExpr → BodyExpr) (e : BodyExpr)
    : BodyExpr :=
  f (e.mapChildren (transform f))

end BodyExpr

/-- A match arm: patterns → expression. -/
structure BodyArm where
  pat : List BodyPat
  rhs : BodyExpr
  deriving Repr

/-- A function body: either pattern-matching arms or
    a direct expression. -/
inductive FnBody where
  /-- Pattern-matching function. -/
  | matchArms (arms : List BodyArm)
  /-- Direct expression (no pattern match needed). -/
  | expr (body : BodyExpr)
  deriving Repr

/-- A precondition applied to specific arguments. -/
structure Precondition where
  /-- The property name. -/
  name : String
  /-- The argument names to apply the property to. -/
  args : List String
  deriving Repr

/-- An exportable function definition. -/
structure FnDef where
  name : String
  symbolDoc : Doc
  doc : Doc
  params : List FieldDef
  returnType : DSLType
  /-- Preconditions that must hold before calling
      this function. -/
  preconditions : List Precondition := []
  body : FnBody
  deriving Repr

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
partial def quoteExpr : BodyExpr → TSyntax `term
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyExpr.var) #[quote n]
  | .natLit n =>
    Syntax.mkApp (mkIdent ``BodyExpr.natLit) #[quote n]
  | .true_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.true_) #[]
  | .false_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.false_) #[]
  | .emptyList =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptyList) #[]
  | .none_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.none_) #[]
  | .some_ e =>
    Syntax.mkApp (mkIdent ``BodyExpr.some_)
      #[quoteExpr e]
  | .mkStruct name args =>
    Syntax.mkApp (mkIdent ``BodyExpr.mkStruct)
      #[quote name, quote (args.map quoteExpr)]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyExpr.cons)
      #[quoteExpr h, quoteExpr t]
  | .append l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.append)
      #[quoteExpr l, quoteExpr r]
  | .dot recv method =>
    Syntax.mkApp (mkIdent ``BodyExpr.dot)
      #[quoteExpr recv, quote method]
  | .flatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.flatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .map list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.map)
      #[quoteExpr list, quote param, quoteExpr body]
  | .mapFn list fn =>
    Syntax.mkApp (mkIdent ``BodyExpr.mapFn)
      #[quoteExpr list, quote fn]
  | .field recv name =>
    Syntax.mkApp (mkIdent ``BodyExpr.field)
      #[quoteExpr recv, quote name]
  | .index list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.index)
      #[quoteExpr list, quoteExpr idx]
  | .indexBang list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.indexBang)
      #[quoteExpr list, quoteExpr idx]
  | .call fn args =>
    Syntax.mkApp (mkIdent ``BodyExpr.call)
      #[quote fn, quote (args.map quoteExpr)]
  | .foldlM fn init list =>
    Syntax.mkApp (mkIdent ``BodyExpr.foldlM)
      #[quote fn, quoteExpr init, quoteExpr list]
  | .lt l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.lt)
      #[quoteExpr l, quoteExpr r]
  | .le l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.le)
      #[quoteExpr l, quoteExpr r]
  | .ltChain es =>
    Syntax.mkApp (mkIdent ``BodyExpr.ltChain)
      #[quote (es.map quoteExpr)]
  | .add l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.add)
      #[quoteExpr l, quoteExpr r]
  | .sub l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.sub)
      #[quoteExpr l, quoteExpr r]
  | .div l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.div)
      #[quoteExpr l, quoteExpr r]
  | .setAll set param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.setAll)
      #[quoteExpr set, quote param, quoteExpr body]
  | .emptySet =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptySet) #[]
  | .setSingleton e =>
    Syntax.mkApp (mkIdent ``BodyExpr.setSingleton)
      #[quoteExpr e]
  | .setUnion l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.setUnion)
      #[quoteExpr l, quoteExpr r]
  | .setFlatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.setFlatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .and l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.and)
      #[quoteExpr l, quoteExpr r]
  | .or l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.or)
      #[quoteExpr l, quoteExpr r]
  | .implies l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.implies)
      #[quoteExpr l, quoteExpr r]
  | .forall_ p b =>
    Syntax.mkApp (mkIdent ``BodyExpr.forall_)
      #[quote p, quoteExpr b]
  | .sorryProof =>
    Syntax.mkApp (mkIdent ``BodyExpr.sorryProof) #[]
  | .leanProof t =>
    Syntax.mkApp (mkIdent ``BodyExpr.leanProof) #[quote t]
  | .match_ scrut arms =>
    let qArms := arms.map fun (pats, rhs) =>
      Syntax.mkApp (mkIdent ``Prod.mk)
        #[quote pats, quoteExpr rhs]
    Syntax.mkApp (mkIdent ``BodyExpr.match_)
      #[quoteExpr scrut, quote qArms]
  | .letIn name val body =>
    Syntax.mkApp (mkIdent ``BodyExpr.letIn)
      #[quote name, quoteExpr val, quoteExpr body]
  | .letBindIn name val body =>
    Syntax.mkApp (mkIdent ``BodyExpr.letBindIn)
      #[quote name, quoteExpr val, quoteExpr body]
  | .ifThenElse c t e =>
    Syntax.mkApp (mkIdent ``BodyExpr.ifThenElse)
      #[quoteExpr c, quoteExpr t, quoteExpr e]
  | .neq l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.neq)
      #[quoteExpr l, quoteExpr r]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

-- ══════════════════════════════════════════════
-- LaTeX rendering
-- ══════════════════════════════════════════════

namespace BodyPat

/-- Render a constructor name as a hyperlinked `\dashuline`
    reference when it matches a known variant. Accepts
    either short (`int`) or qualified (`Value.int`) forms;
    the label uses the short name. -/
private def ctorRef
    (knownCtors : String → Bool) (n : String) : LatexMath :=
  let shortName := (n.splitOn ".").getLast?.getD n
  if knownCtors shortName then
    .raw s!"\\text\{\\hyperlink\{ctor:{shortName}}\
            \{\\dashuline\{{n}}}}"
  else .text (.raw n)

partial def toLatexMath
    (ctorDisplay : String → Option LatexMath)
    (knownCtors : String → Bool := fun _ => false)
    : BodyPat → LatexMath
  | .wild => .raw "\\_"
  | .var n => .escaped n
  | .ctor "⟨⟩" args =>
    .delimited "(" ")"
      (LatexMath.intercalate (.raw ",~")
        (args.map (toLatexMath ctorDisplay knownCtors)))
  | .ctor n args =>
    if args.isEmpty then
      match ctorDisplay n with
      | some display => display
      | none => ctorRef knownCtors n
    else
      let argParts :=
        args.map (toLatexMath ctorDisplay knownCtors)
      .seq [ ctorRef knownCtors n, .raw "("
           , LatexMath.intercalate (.raw ",~") argParts
           , .raw ")" ]
  | .nil => .raw "[]"
  | .cons h t =>
    let rec flatten : BodyPat → Option (List BodyPat)
      | .nil => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      .seq [ .raw "["
           , LatexMath.intercalate (.raw ",~")
               (elems.map
                 (toLatexMath ctorDisplay knownCtors))
           , .raw "]" ]
    | none =>
      .seq [ h.toLatexMath ctorDisplay knownCtors
           , .raw " :: "
           , t.toLatexMath ctorDisplay knownCtors ]
  | .natLit n => .raw (toString n)

end BodyPat

namespace BodyExpr

partial def toLatexMath
    (fnName : String)
    (varDisplay : String → Option LatexMath :=
      fun _ => none)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (isProperty : Bool := false)
    (knownFns : String → Bool := fun _ => false)
    (knownCtors : String → Bool := fun _ => false)
    : BodyExpr → LatexMath :=
  let go := toLatexMath fnName varDisplay ctorDisplay
    isProperty knownFns knownCtors
  let ctorRef := BodyPat.ctorRef knownCtors
  let fnRef (fn : String) : LatexMath :=
    -- Strip any namespace prefix (e.g. `Memory.store` →
    -- `store`) so qualified calls still resolve to the
    -- labelled function. Fall back to a constructor
    -- reference (e.g. `Value.int`) when the name does
    -- not match a known function.
    let shortName := (fn.splitOn ".").getLast?.getD fn
    if knownFns shortName then
      .raw s!"\\text\{\\hyperref[fn:{shortName}]\
              \{\\dashuline\{{fn}}}}"
    else ctorRef fn
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none => .escaped n
  | .natLit n => .raw (toString n)
  | .true_ =>
    if isProperty then .cmd "top"
    else .text (.raw "true")
  | .false_ =>
    if isProperty then .cmd "bot"
    else .text (.raw "false")
  | .emptyList => .raw "[]"
  | .none_ => .text (.raw "None")
  | .some_ e =>
    .seq [.text (.raw "Some"), .raw "(", go e, .raw ")"]
  | .mkStruct name args =>
    if name == "" then
      .delimited "(" ")"
        (LatexMath.intercalate (.raw ",~")
          (args.map go))
    else
      .seq [ ctorRef name, .raw "("
           , LatexMath.intercalate (.raw ",~")
               (args.map go)
           , .raw ")" ]
  | .cons h t =>
    -- Flatten cons chains ending in `emptyList` into a
    -- list literal `[e₁, e₂, …]`.
    let rec flatten : BodyExpr → Option (List BodyExpr)
      | .emptyList => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      .seq [ .raw "["
           , LatexMath.intercalate (.raw ",~")
               (elems.map go)
           , .raw "]" ]
    | none => .seq [go h, .raw " :: ", go t]
  | .append l r =>
    .seq [ go l, .raw " \\mathbin{\\texttt{++}} "
         , go r ]
  | .dot recv "length" =>
    .seq [.raw "|", go recv, .raw "|"]
  | .dot recv "toNat" =>
    .seq [go recv, .raw "~\\text{as}~", .mathbb (.raw "N")]
  | .dot recv method =>
    .seq [fnRef method, .raw "(", go recv
         , .raw ")"]
  | .flatMap list param body =>
    .seq [ go list, .raw ".\\text{flatMap}("
         , .cmd "lambda", .raw " "
         , .escaped param, .raw ".~", go body
         , .raw ")" ]
  | .map list param body =>
    .seq [ go list, .raw ".\\text{map}("
         , .cmd "lambda", .raw " "
         , .escaped param, .raw ".~", go body
         , .raw ")" ]
  | .mapFn list fn =>
    .seq [ go list, .raw ".\\text{map}("
         , fnRef fn, .raw ")" ]
  | .field recv name =>
    .seq [go recv, .raw ".", .text (.raw name)]
  | .index list idx =>
    .seq [go list, .raw "[", go idx, .raw "]"]
  | .indexBang list idx =>
    .seq [go list, .raw "[", go idx, .raw "]"]
  | .call "listSet" [a, b, c] =>
    .seq [ go a, .raw "[", go b, .raw " \\mapsto "
         , go c, .raw "]" ]
  | .call "mapGet" [a, b] =>
    .seq [ go a, .raw "[", go b, .raw "]" ]
  | .call fn args =>
    .seq [ fnRef fn, .raw "("
         , LatexMath.intercalate (.raw ",~")
             (args.map go)
         , .raw ")" ]
  | .foldlM fn init list =>
    .seq [ fnRef fn, .raw "^*(", go init
         , .raw ",~", go list, .raw ")" ]
  | .lt l r => .binop "<" (go l) (go r)
  | .le l r => .binop "\\leqslant" (go l) (go r)
  | .ltChain es =>
    LatexMath.intercalate (.raw " < ") (es.map go)
  | .add l r => .binop "+" (go l) (go r)
  | .sub l r => .binop "-" (go l) (go r)
  | .div l r => .binop "/" (go l) (go r)
  | .setAll set param body =>
    .seq [ .cmd "forall", .raw " "
         , .escaped param, .raw " "
         , .cmd "in", .raw " ", go set
         , .raw ",~", go body ]
  | .emptySet => .cmd "emptyset"
  | .setSingleton e =>
    .delimited "\\{" "\\}" (go e)
  | .setUnion l r =>
    .binop "\\cup" (go l) (go r)
  | .setFlatMap list param body =>
    .seq [ .sub (.cmd "bigcup")
             (.seq [.escaped param, .raw " "
                   , .cmd "in", .raw " ", go list])
         , .raw " ", go body ]
  | .and l r => .binop "\\land" (go l) (go r)
  | .or l r => .binop "\\lor" (go l) (go r)
  | .implies l r => .binop "\\to" (go l) (go r)
  | .forall_ p b =>
    .seq [ .cmd "forall", .raw " "
         , .escaped p, .raw ",~", go b ]
  | .sorryProof => .seq []
  | .leanProof _ => .seq []
  | .match_ scrut arms =>
    let noCtor : String → Option LatexMath :=
      fun _ => Option.none
    let rows := arms.map fun (pats, rhs) =>
      let patMath := LatexMath.intercalate (.raw ",~")
        (pats.map (BodyPat.toLatexMath noCtor))
      [go rhs, .seq [ .text (.raw "if~")
                     , patMath ]]
    .seq [ .text (.raw "match~")
         , go scrut
         , .raw ": "
         , .delimited "\\left\\{" "\\right."
             (.array Option.none "ll" rows) ]
  | .letIn name val body =>
    .seq [ .text (.raw "let~"), .escaped name
         , .raw " := ", go val, .raw ";~"
         , go body ]
  | .letBindIn name val body =>
    .seq [ .text (.raw "let~"), .escaped name
         , .raw " ", .cmd "leftarrow", .raw " "
         , go val, .raw ";~", go body ]
  | .ifThenElse c t e =>
    .seq [ .text (.raw "if~"), go c
         , .raw "~", .text (.raw "then~"), go t
         , .raw "~", .text (.raw "else~"), go e ]
  | .neq l r => .binop "\\neq" (go l) (go r)

end BodyExpr

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    .seq [.plain s!"{p.name} : ", p.ty.toDoc .normal]
  .seq [ f.symbolDoc, .plain "(",
    Doc.intercalate (.plain ", ") paramDocs,
    .plain ") → ", f.returnType.toDoc .normal ]

private partial def exprLinesTop
    (fnName : String)
    (ctorDisplay : String → Option LatexMath)
    (isProperty : Bool)
    (knownFns : String → Bool)
    (knownCtors : String → Bool)
    (e : BodyExpr) (depth : Nat) : List Latex :=
  let noDisp : String → Option LatexMath := fun _ => none
  let goExpr := BodyExpr.toLatexMath fnName
    noDisp ctorDisplay isProperty knownFns knownCtors
  let mkIndent (n : Nat) : LatexMath :=
    .raw (String.join (List.replicate n "\\hskip1.5em "))
  match e with
  | .letIn name val rest =>
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , .escaped name
             , .raw " := "
             , goExpr val ])) ]
    letLine :: exprLinesTop fnName ctorDisplay isProperty
      knownFns knownCtors rest depth
  | .letBindIn name val rest =>
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , .escaped name
             , .raw " ", .cmd "leftarrow", .raw " "
             , goExpr val ])) ]
    letLine :: exprLinesTop fnName ctorDisplay isProperty
      knownFns knownCtors rest depth
  | .ifThenElse cond t e =>
    let ifLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "if~")
             , goExpr cond
             , .raw "~", .text (.raw "then") ])) ]
    let thenLines := exprLinesTop fnName ctorDisplay
      isProperty knownFns knownCtors t (depth + 1)
    let elseLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "else") ])) ]
    let elseLines := exprLinesTop fnName ctorDisplay
      isProperty knownFns knownCtors e (depth + 1)
    ifLine :: thenLines ++ elseLine :: elseLines
  | .match_ scrut matchArms =>
    let headerLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "match~")
             , goExpr scrut
             , .raw ":" ])) ]
    let armBlocks := matchArms.flatMap
      fun (pats, rhs) =>
        let patMath := LatexMath.intercalate
          (.raw ",~")
          (pats.map
            (BodyPat.toLatexMath noDisp knownCtors))
        let isSimple := match rhs with
          | .letIn .. => false
          | .letBindIn .. => false
          | .match_ .. => false
          | .ifThenElse .. => false
          | _ => true
        if isSimple then
          let caseLine : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     mkIndent (depth + 1)
                   , .text (.raw "case~")
                   , patMath
                   , .raw ": "
                   , goExpr rhs ])) ]
          [caseLine]
        else
          let caseLine : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     mkIndent (depth + 1)
                   , .text (.raw "case~")
                   , patMath
                   , .raw ":" ])) ]
          caseLine :: exprLinesTop fnName ctorDisplay
            isProperty knownFns knownCtors rhs (depth + 2)
    headerLine :: armBlocks
  | e =>
    [.seq [ .raw "    "
          , Latex.state (.inlineMath (.seq [
              mkIndent depth, goExpr e ])) ]]

/-- Render the function as a LaTeX algorithm. -/
def formalDefLatex
    (f : FnDef)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (variants : List VariantDef := [])
    (isProperty : Bool := false)
    (knownFns : String → Bool := fun _ => false)
    (knownCtors : String → Bool := fun _ => false)
    : Latex :=
  let paramParts : List Latex := f.params.map fun p =>
    Latex.seq [.text p.name, .raw " : ",
               (p.ty.toDoc .normal).toLatex]
  let paramSig : Latex :=
    .seq (paramParts.intersperse (.raw ", "))
  let caption : Latex :=
    if isProperty then
      .seq [.raw "Property ", .text f.name,
            .raw "(", paramSig, .raw ")"]
    else
      let retTy := (f.returnType.toDoc .normal).toLatex
      .seq [.text f.name, .raw "(",
            paramSig, .raw ") ",
            .inlineMath (.cmd "to"), .raw " ",
            retTy]
  let bodyLines : List Latex := match f.body with
    | .matchArms arms => arms.flatMap fun arm =>
      let ctorName := arm.pat.head?.bind fun p =>
        match p with | .ctor n _ => some n | _ => none
      let varDisplay : String → Option LatexMath :=
        fun varName =>
          match ctorName with
          | none => none
          | some cn =>
            let variant := variants.find?
              (·.name.name == cn)
            match variant with
            | none => none
            | some v => v.display.findSome? fun dp =>
              match dp with
              | .arg n sym =>
                if n == varName then
                  some (MathDoc.toLatexMath sym)
                else none
              | _ => none
      let patMath := LatexMath.intercalate (.raw ",~")
        (arm.pat.map
          (BodyPat.toLatexMath ctorDisplay knownCtors))
      let goExpr := BodyExpr.toLatexMath f.name
        varDisplay ctorDisplay isProperty knownFns
        knownCtors
      let rec rhsLines : BodyExpr → List Latex
        | .letBindIn name val rest =>
          .seq [ .raw "    "
               , Latex.state (.inlineMath (.seq [
                   .raw "\\hskip1.5em "
                 , .text (.raw "let~")
                 , .escaped name
                 , .raw " ", .cmd "leftarrow", .raw " "
                 , goExpr val ])) ]
          :: rhsLines rest
        | .letIn name val rest =>
          .seq [ .raw "    "
               , Latex.state (.inlineMath (.seq [
                   .raw "\\hskip1.5em "
                 , .text (.raw "let~")
                 , .escaped name
                 , .raw " := "
                 , goExpr val ])) ]
          :: rhsLines rest
        | .ifThenElse cond t e =>
          let ifLine : Latex := .seq
            [ .raw "    "
            , Latex.state (.inlineMath (.seq [
                .raw "\\hskip1.5em "
              , .text (.raw "if~")
              , goExpr cond
              , .raw "~", .text (.raw "then") ])) ]
          let branchLine (label : String)
              (body : BodyExpr) : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     .raw "\\hskip3em "
                   , .text (.raw label)
                   , goExpr body ])) ]
          let elseHeader : Latex := .seq
            [ .raw "    "
            , Latex.state (.inlineMath (.seq [
                .raw "\\hskip1.5em "
              , .text (.raw "else") ])) ]
          [ ifLine, branchLine "" t, elseHeader
          , branchLine "" e ]
        | e =>
          [.seq [ .raw "    "
                , Latex.state (.inlineMath (.seq [
                    .raw "\\hskip1.5em ", goExpr e ])) ]]
      let isSimple := match arm.rhs with
        | .letBindIn .. => false
        | .letIn .. => false
        | .ifThenElse .. => false
        | .match_ .. => false
        | _ => true
      if isSimple then
        let rhsMath := arm.rhs.toLatexMath f.name
          varDisplay ctorDisplay isProperty knownFns
          knownCtors
        [.seq [ .raw "    "
             , Latex.state (.seq [
                 .textbf (.raw "case"), .raw " "
               , .inlineMath patMath
               , .raw ": "
               , .inlineMath rhsMath ]) ]]
      else
        let caseLine : Latex :=
          .seq [ .raw "    "
               , Latex.state (.seq [
                   .textbf (.raw "case"), .raw " "
                 , .inlineMath patMath
                 , .raw ":" ]) ]
        caseLine :: rhsLines arm.rhs
    | .expr body => exprLinesTop f.name ctorDisplay
        isProperty knownFns knownCtors body 0
  let precondLines : List Latex :=
    f.preconditions.map fun pc =>
      let argsMath := LatexMath.intercalate
        (.raw ", ") (pc.args.map LatexMath.escaped)
      .seq [ .raw "    "
           , Latex.require_ (.inlineMath
               (.seq [.escaped pc.name
                     , .raw "(", argsMath
                     , .raw ")"])) ]
  let allLines := precondLines ++ bodyLines
  let descBlock : List Latex :=
    if f.doc.toPlainText.isEmpty then []
    else [.textit f.doc.toLatex, .newline]
  .env "algorithm" (.seq [
    Latex.caption caption, .newline,
    .raw s!"\\label\{fn:{f.name}}", .newline,
    .seq descBlock,
    .env "algorithmic"
      (.seq [Latex.lines allLines, .newline]),
    .newline
  ])

/-- Render for non-LaTeX (Doc-based). -/
def algorithmDoc (f : FnDef) : Doc :=
  let noDisplay : String → Option LatexMath :=
    fun _ => none
  let header := Doc.seq
    [ f.doc, .plain " ", f.shortSig ]
  let cases := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map fun p =>
          (p.toLatexMath noDisplay).render)
      let rhsStr := (arm.rhs.toLatexMath f.name
        noDisplay noDisplay).render
      Doc.plain s!"case {patStr}: return {rhsStr}"
    | .expr body =>
      let rhsStr := (body.toLatexMath f.name
        noDisplay noDisplay).render
      [Doc.plain s!"return {rhsStr}"]
  .seq [header, .line, .itemize cases]

end FnDef
