import Core.Export.Latex
import Core.Dsl.DeriveQuote
import Core.Dsl.Types.FnAppStyle
import Core.Dsl.Types.FormatHint
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.BodyPat
import Core.Dsl.Types.RenderCtx
import Core.Dsl.DslType
import Core.Meta.BaseFunctor
import Core.LeanAST

deriving instance Lean.Quote for IneqOp

/-- A variable identifier in the DSL. -/
structure VarIdent where
  /-- The identifier name. -/
  name : String
  deriving Repr, Inhabited, Lean.Quote

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
  /-- Lambda: `fun param => body`. -/
  | lambda (param : VarIdent) (body : DslExpr)
  /-- List flat-map: `list.flatMap fn`. -/
  | flatMap (list : DslExpr) (fn : DslExpr)
  /-- List map: `list.map fn`. -/
  | map (list : DslExpr) (fn : DslExpr)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : DslExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : DslExpr) (idx : DslExpr)
  /-- Infallible list indexing: `list[idx]`. -/
  | indexBang (list : DslExpr) (idx : DslExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : DslExpr) (args : List DslExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : DslExpr) (init : DslExpr)
      (list : DslExpr)
  /-- Less-than comparison: `lhs < rhs`. -/
  | lt (lhs : DslExpr) (rhs : DslExpr)
  /-- Less-than-or-equal: `lhs ≤ rhs`. -/
  | le (lhs : DslExpr) (rhs : DslExpr)
  /-- Chained inequality: `a < b ≤ c < …`.
      Each operator in `ops` connects successive
      expressions; `ops` has one fewer element than
      `exprs`. -/
  | ineqChain (ops : List IneqOp) (exprs : List DslExpr)
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
  /-- Universal quantifier with one or more binder groups:
      `∀ b₁, b₂, …, bₙ, body`. Each group is a non-empty
      list of variables sharing an optional type annotation:
      `(["pr"], some "Program")` renders as `pr ∈ Program`,
      `(["p", "p'"], some "Place")` renders as `p p' ∈ Place`,
      and `(["x"], none)` renders as a bare `x`. The LaTeX
      backend produces `∀ pr ∈ Program, ar ∈ AnalysisResults,
      p p' ∈ Place, body`; the Lean backend produces
      `∀ (pr : Program) (ar : AnalysisResults) (p p' : Place),
      body`. Type names are bare references to existing types
      (e.g. `Program`, `Machine`); they are not parsed further. -/
  | forall_ (binders : List (List String × Option String))
      (body : DslExpr)
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
  /-- `let pat := val ; body`. The binder is a `BodyPat` so
      that tuple destructuring (`let ⟨a, b⟩ := …`) is expressible
      in addition to the simple `let x := …` form. -/
  | letIn (pat : BodyPat) (val : DslExpr) (body : DslExpr)
  /-- `let pat ← val ; body` (monadic bind on Option). The
      binder is a `BodyPat` so that destructuring binds
      (`let ⟨a, b⟩ ← …`) are expressible in addition to the
      simple `let n ← …` form. -/
  | letBindIn (pat : BodyPat) (val : DslExpr) (body : DslExpr)
  /-- `if cond then t else e`. -/
  | ifThenElse (cond : DslExpr) (t : DslExpr) (e : DslExpr)
  /-- Inequality: `lhs ≠ rhs`. -/
  | neq (lhs : DslExpr) (rhs : DslExpr)
  /-- Decidable / `BEq` equality: `lhs == rhs`. -/
  | eq (lhs : DslExpr) (rhs : DslExpr)
  /-- Propositional equality: `lhs = rhs`. Used in property
      bodies and inductive-property premises where a `Prop`
      is required (rather than a `Bool`). -/
  | propEq (lhs : DslExpr) (rhs : DslExpr)
  /-- List existential: `list.any fun param => body`. -/
  | anyList (list : DslExpr) (param : String)
      (body : DslExpr)
  /-- Set/List membership: `elem ∈ col`. -/
  | memberOf (elem : DslExpr) (col : DslExpr)
  /-- Functional struct update: `recv[fieldName => newValue]`
      — a copy of `recv` with the named field replaced. The
      receiver's type is inferred from the surrounding
      context (function parameters) at codegen time. -/
  | structUpdate (recv : DslExpr) (fieldName : String)
      (newValue : DslExpr)
  /-- Presentation-only formatting hint. The LaTeX renderer
      consumes the hint (e.g. inserts a soft line break);
      Lean and Rust translations pass `body` through
      unchanged. -/
  | formatHint (hint : FormatHint) (body : DslExpr)
  deriving Repr, Inhabited, Lean.Quote

-- Generate `DslExprF`, `project`, `embed`, `map`, `mapM`, `cata`, `cataM`,
-- `para`, `paraM`. See `Core.Meta.BaseFunctor` for details.
derive_base_functor DslExpr

/-- A field/method access in the DSL. -/
structure DslField where
  /-- The receiver expression. -/
  recv : DslExpr
  /-- The field or method name. -/
  method : String
  deriving Repr, Inhabited

/-- Convert a variable identifier to a
    variable-reference expression. -/
instance : Coe VarIdent DslExpr where
  coe i := .var i.name

/-- Convert a field access to a dot expression. -/
instance : Coe DslField DslExpr where
  coe f := .dot f.recv f.method

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
  | .forall_ bs b => .forall_ bs (f b)
  -- Binary
  | .lambda p b => .lambda p (f b)
  | .cons h t => .cons (f h) (f t)
  | .append l r => .append (f l) (f r)
  | .flatMap l fn => .flatMap (f l) (f fn)
  | .map l fn => .map (f l) (f fn)
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
  | .eq l r => .eq (f l) (f r)
  | .propEq l r => .propEq (f l) (f r)
  | .memberOf l r => .memberOf (f l) (f r)
  -- Ternary (with String parameter)
  | .anyList l p b => .anyList (f l) p (f b)
  | .setAll s p b => .setAll (f s) p (f b)
  | .setFlatMap l p b => .setFlatMap (f l) p (f b)
  | .letIn p v b => .letIn p (f v) (f b)
  | .letBindIn p v b => .letBindIn p (f v) (f b)
  | .ifThenElse c t e => .ifThenElse (f c) (f t) (f e)
  | .foldlM fn init list => .foldlM (f fn) (f init) (f list)
  | .formatHint h b => .formatHint h (f b)
  -- List children
  | .mkStruct n args => .mkStruct n (args.map f)
  | .call fn args => .call (f fn) (args.map f)
  | .ineqChain ops es => .ineqChain ops (es.map f)
  -- Match (recurse into scrutinee and arm RHSs)
  | .match_ s arms =>
    .match_ (f s) (arms.map fun (p, rhs) => (p, f rhs))
  | .structUpdate r fld v => .structUpdate (f r) fld (f v)

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
    (ctx : RenderCtx := {})
    (varDisplay : String → Option MathDoc :=
      fun _ => none)
    (isProperty : Bool := false)
    : DslExpr → MathDoc :=
  let go := toDoc fnName ctx varDisplay isProperty
  let ctorRef := BodyPat.ctorRef ctx.resolveCtor
  -- Link a struct constructor to its type definition. Falls
  -- back to `ctorRef` so that enum-variant constructors remain
  -- linked to their ctor target.
  let structRef (n : String) : MathDoc :=
    if ctx.knownTypes n then
      .doc (.link (.plain n) s!"#type:{n}")
    else ctorRef n
  let fnRef (fn : String) : MathDoc :=
    -- Fn-reference resolution, in order:
    --  (1) If the call is qualified (`X.y`) and `X.y` matches a
    --      known `fn:` anchor, link to `#fn:X.y`. This handles
    --      explicit qualifications at the call site.
    --  (2) If the short name resolves to an unambiguous known
    --      fn, link to `#fn:shortName`.
    --  (3) If the short name is ambiguous, try to resolve it
    --      against the enclosing function's module — a bare
    --      `meet` inside `PCG.Owned.InitTree` resolves to
    --      `#fn:InitTree.meet`. This is the best-effort
    --      resolution for unqualified ambiguous calls.
    --  (4) Otherwise fall back to a constructor reference.
    let shortName := (fn.splitOn ".").getLast?.getD fn
    let mkLinkAs (target : String) (display : String) : MathDoc :=
      .doc (.link (.plain (Doc.fnNameDisplay display))
        s!"#fn:{target}")
    let mkLink (target : String) : MathDoc :=
      mkLinkAs target fn
    if fn != shortName && ctx.knownFnAnchors fn then
      mkLink fn
    else if ctx.knownFns shortName && !ctx.ambiguousFns shortName then
      -- Short name unambiguously resolves to a registered fn:
      -- drop any qualifier the call site used (e.g. `OwnedState.initial`
      -- → `initial`) so the display matches the link target.
      mkLinkAs shortName shortName
    else if ctx.knownFns shortName then
      match ctx.currentFnModule with
      | some mod =>
        let candidate := s!"{mod}.{shortName}"
        if ctx.knownFnAnchors candidate then
          mkLink candidate
        else
          .doc (.underline .dashed (.plain (Doc.fnNameDisplay fn)))
      | none =>
        .doc (.underline .dashed (.plain (Doc.fnNameDisplay fn)))
    else ctorRef fn
  -- A trailing keyword like `let ` / `if ` / `match ` with
  -- a non-breaking space after the word.
  let keyword (s : String) : MathDoc :=
    .seq [MathDoc.text s, .sym .space]
  -- Whether the part to the LEFT of an `.arg` slot bounds the
  -- argument on the left — i.e. blocks juxtaposition with the
  -- preceding context. Any non-whitespace lit or sym (brackets,
  -- commas, operators) bounds; bare space, `none` (handled by
  -- the caller as the start-of-template), and another `.arg`
  -- do not.
  let displayPartLeftDelimits : DisplayPart → Bool
    | .lit m => match m with
      | .raw s => !s.trim.isEmpty
      | .sym .space => false
      | _ => true
    | .arg _ _ => false
  -- Whether the part to the RIGHT of an `.arg` slot would
  -- "left-attach" to the argument and grab it as a sub-expression
  -- (like a subscript `[…]` or a function-call paren `(…)`). Such
  -- a part forces protective parens around a compound argument
  -- so e.g. `(programEntryStateAt par … m)[p, b]` doesn't
  -- collapse to `programEntryStateAt par … m[p, b]`. Other
  -- delimiters (`,`, `]`, `)`, infix operators, …) bound the
  -- argument cleanly and don't trigger the wrap.
  let displayPartLeftAttaches : DisplayPart → Bool
    | .lit m => match m with
      | .raw s =>
        let t := s.trim
        t.startsWith "[" || t.startsWith "("
      | .sym .lbracket | .sym .lparen => true
      | _ => false
    | .arg _ _ => true
  -- Whether an expression needs parentheses when placed in a
  -- juxtaposition position (e.g. as the argument of `Some`, a
  -- unary defEnum constructor, or a fn-display template).
  -- Atomic-looking forms render without parens; everything else
  -- (infix operators, calls, control flow, lambdas, …) gets
  -- wrapped so that `Some (sz + off)` does not collapse to the
  -- ambiguous `Some sz + off`.
  let rec needsParen : DslExpr → Bool
    | .var _ | .natLit _ | .true_ | .false_ | .none_ => false
    | .emptyList | .emptySet => false
    | .setSingleton _ => false
    | .field .. => false
    -- `.dot` is atomic in `Rust` style (renders as
    -- `method(recv)`) but juxtaposed in `Haskell` style
    -- (`method recv`) — a juxtaposition needs parens when
    -- placed inside another juxtaposition, otherwise
    -- `toSet (operandPlace x)` collapses to the ambiguous
    -- `toSet operandPlace x`.
    | .dot .. => PRESENTATION_FN_APP_STYLE == .Haskell
    | .index .. | .indexBang .. => false
    | .structUpdate .. => false
    | .mkStruct "" _ => false
    | .cons .. => false
    | .sorryProof | .leanProof _ => false
    -- A call to an `implicit` defFn renders as just its lone
    -- argument, so its paren-need is whatever the argument's is.
    | .call (.var n) [a] =>
      let short := (n.splitOn ".").getLast?.getD n
      if ctx.implicitFns short then needsParen a else true
    | _ => true
  -- Render a list of display-template parts, substituting each
  -- `.arg` via `resolveArg`. Protective parens are dropped around
  -- a compound substituted argument when the slot is bounded on
  -- both sides: the preceding part bounds the argument on the
  -- left (any non-whitespace lit) and the following part doesn't
  -- left-attach (no `[`, `(`, …). The start-of-template
  -- boundary is treated as bounded since outer contexts
  -- (implication chains, surrounding operators, …) typically
  -- supply a delimiter; the end-of-template boundary likewise.
  -- Net effect: `par[(currBody m)]` renders as `par[currBody m]`
  -- and `(currPC m) ∈ ar` renders as `currPC m ∈ ar`, while
  -- `(programEntryStateAt par b pc)[p, b] ≐ E` keeps its outer
  -- parens because `[` would otherwise grab the trailing arg.
  let renderDisplayParts
      (parts : List DisplayPart)
      (resolveArg : String → Option (DslExpr × MathDoc))
      : MathDoc :=
    let arr := parts.toArray
    let renderedParts : List MathDoc :=
      arr.zipIdx.toList.map fun (p, i) =>
        match p with
        | .lit d => d
        | .arg name _ =>
          match resolveArg name with
          | some (e, d) =>
            let prev := if i == 0 then none else arr[i - 1]?
            let next := arr[i + 1]?
            let leftBounded := match prev with
              | none => true
              | some part => displayPartLeftDelimits part
            let rightBounded := match next with
              | none => true
              | some part => !displayPartLeftAttaches part
            if needsParen e && !(leftBounded && rightBounded)
            then MathDoc.paren d
            else d
          | none => MathDoc.text name
    MathDoc.seq renderedParts
  -- Resolve a variable reference to a variant's display when it
  -- names a qualified constructor — e.g. `Capability.none`
  -- should render as `∅` rather than the literal text
  -- `Capability.none`. Only qualified names (containing `.`)
  -- are rewritten: a bare short name in value position almost
  -- always refers to a local binder rather than a variant, and
  -- short-name lookup could collide across enums (e.g. the
  -- `none` variant exists on several types). Nullary variants
  -- use the variant's full display template; variants with
  -- arguments still pass through to `.raw` to avoid silently
  -- dropping unapplied arguments.
  let varToVariantDoc (n : String) : Option MathDoc :=
    -- Accept both qualified names (`Capability.none`) and
    -- the anonymous-constructor sugar `.none` — strip the
    -- leading `.` so the bare variant name resolves.
    let lookupName :=
      if n.startsWith "." then (n.drop 1).toString else n
    if !n.contains '.' then none
    else match ctx.resolveVariant lookupName with
      | some v =>
        if v.args.isEmpty then
          match ctx.resolveCtor lookupName with
          | some qualified =>
            some (.doc (.link (.math v.displayMathDoc)
              s!"#ctor:{qualified}"))
          | none => some v.displayMathDoc
        else none
      | none => none
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none =>
      match varToVariantDoc n with
      | some md => md
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
    -- Render `Some x` like a unary defEnum constructor:
    -- juxtaposition with a space, parens only around
    -- compound arguments (calls, named-struct literals,
    -- infix operators, …) so bare identifiers stay
    -- paren-free while `Some (sz + off)` remains
    -- unambiguous.
    let argDoc := go e
    let arg := if needsParen e then MathDoc.paren argDoc
               else argDoc
    .seq [MathDoc.text "Some", .sym .space, arg]
  | .mkStruct name args =>
    let argDocs := args.map go
    if name == "" then
      -- Anonymous tuple literal: use angle brackets so it
      -- visually differs from a function-call argument list.
      .seq [ .sym .langle
           , mathIntercalate (.sym .comma) argDocs
           , .sym .rangle ]
    else
      -- A constructor of a struct with a custom display template
      -- renders using that template, with each `#field` reference
      -- replaced by the rendered argument at the matching
      -- positional slot. This produces the pretty form (e.g.
      -- `{R} p {None}` for a `PlaceTriple`) instead of the
      -- Lean-source `PlaceTriple(p, R, None)`. Compound arguments
      -- (calls / nested constructors / infix operators / …) are
      -- wrapped in parentheses so juxtapositions remain
      -- unambiguous; the predicate is the shared `needsParen`.
      let templated : Option MathDoc :=
        ctx.resolveStructDisplay name |>.bind fun (parts, fields) =>
          if fields.length == args.length then
            let argMap : List (String × DslExpr × MathDoc) :=
              (fields.zip args).zip argDocs |>.map
                fun ((f, e), d) => (f, e, d)
            let resolveArg (fname : String) :
                Option (DslExpr × MathDoc) :=
              argMap.find? (·.1 == fname) |>.map
                fun (_, e, d) => (e, d)
            some (renderDisplayParts parts resolveArg)
          else none
      match templated with
      | some md => md
      | none =>
        .seq [ structRef name
             , MathDoc.paren
                 (mathIntercalate (.sym .comma) argDocs) ]
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
    -- `recv.method` desugars to a one-argument function call:
    -- follow `PRESENTATION_FN_APP_STYLE` so `Haskell` renders
    -- as `method recv` (with parens around compound receivers)
    -- and `Rust` keeps the existing `method(recv)` form.
    let recvDoc := go recv
    if PRESENTATION_FN_APP_STYLE == .Haskell then
      let arg := if needsParen recv then MathDoc.paren recvDoc
                 else recvDoc
      .seq [fnRef method, .sym .space, arg]
    else
      .seq [fnRef method, MathDoc.paren recvDoc]
  | .lambda param body =>
    .seq [ .sym .lambda, .raw param.name, .sym .dot
         , .sym .space, go body ]
  | .flatMap list fn =>
    .seq [ go list, .sym .dot, MathDoc.text "flatMap"
         , MathDoc.paren (go fn) ]
  | .map list fn =>
    .seq [ go list, .sym .dot, MathDoc.text "map"
         , MathDoc.paren (go fn) ]
  | .field recv name =>
    .seq [go recv, .sym .dot, MathDoc.text name]
  | .index list idx =>
    .seq [go list, MathDoc.bracket (go idx)]
  | .indexBang list idx =>
    .seq [go list, MathDoc.bracket (go idx)]
  | .call (.var "listSet") [a, b, c] =>
    .seq [ go a, MathDoc.bracket
             (.seq [go b, .sym .mapsto, go c]) ]
  | .call (.var "mapGet") [a, b] =>
    .seq [go a, MathDoc.bracket (go b)]
  | .call (.var "mapAt") [a, b] =>
    -- `mapAt m k` is the panic-on-missing variant of `mapGet`;
    -- render the same as `mapGet` (`m[k]`) since the math
    -- presentation doesn't distinguish.
    .seq [go a, MathDoc.bracket (go b)]
  | .call (.var "mapInsert") [a, b, c] =>
    -- `mapInsert m k v` renders as `m[k ↦ v]`.
    .seq [ go a, MathDoc.bracket
             (.seq [go b, .sym .mapsto, go c]) ]
  | .call (.var "mapRemove") [a, b] =>
    -- `mapRemove m k` renders as `m \ {k}` using LaTeX's
    -- `\setminus` for set difference.
    .seq [go a, rawMath " \\setminus ", MathDoc.brace (go b)]
  | .call (.var "mapEmpty") [] => .sym .emptySet
  | .call (.var "mapSingleton") [a] =>
    -- `mapSingleton ⟨k, v⟩` is an anonymous-tuple call;
    -- render the body in brace-set notation `{k ↦ v}`.
    match a with
    | .mkStruct "" [k, v] =>
      MathDoc.brace (.seq [go k, .sym .mapsto, go v])
    | _ => MathDoc.brace (go a)
  | .call (.var "mapSingleton") [k, v] =>
    MathDoc.brace (.seq [go k, .sym .mapsto, go v])
  | .call (.var "mapUnionSets") [a, b] =>
    .seq [go a, .sym .cup, go b]
  | .call (.var "mapUnionSets") [arg] =>
    -- `mapUnionSets ⟨a, b⟩` (paired call form).
    match arg with
    | .mkStruct "" [a, b] => .seq [go a, .sym .cup, go b]
    | _ => .seq [MathDoc.text "mapUnionSets",
                 MathDoc.paren (go arg)]
  | .call fn args =>
    -- Drop the trailing N args corresponding to a registered
    -- function's precondition proofs. The DSL surface form
    -- always supplies one argument per precondition (either
    -- a `lean_proof("…")` placeholder or a regular variable
    -- bound elsewhere), so trimming by count handles both
    -- cases uniformly. Without this, an inductive-property
    -- rule like `step ‹m'', h›` would render as `step m'' h`
    -- — the proof argument is necessary for in-process Lean
    -- elaboration but carries no information in the
    -- presentation.
    let precondCount : Nat := match fn with
      | .var n =>
        let short := (n.splitOn ".").getLast?.getD n
        ctx.fnPrecondCount short
      | _ => 0
    let nonProofArgs :=
      args.take (args.length - precondCount)
    -- Then drop any remaining proof-shaped expressions (e.g.
    -- a stray `lean_proof("…")` in non-precondition position):
    -- they would render as empty math and leave dangling
    -- commas.
    let visibleArgs := nonProofArgs.filter fun
      | .sorryProof => false
      | .leanProof _ => false
      | _ => true
    -- A call whose head names an `implicit` defFn renders as
    -- its lone argument alone — the function head is dropped
    -- from the LaTeX presentation. Implicit defFns are
    -- constrained to a single explicit parameter at
    -- elaboration time, so we can safely unwrap the first
    -- visible argument.
    let implicitFnDoc : Option MathDoc := match fn, visibleArgs with
      | .var n, [a] =>
        let short := (n.splitOn ".").getLast?.getD n
        if ctx.implicitFns short then some (go a) else none
      | _, _ => none
    -- A call whose head names a known enum variant renders
    -- using the variant's display template, with each arg
    -- reference replaced by the rendered argument. This
    -- produces the natural `leaf cap` / `internal (fields fs)`
    -- form instead of the Lean-source `.leaf(cap)`. Accepts
    -- both the qualified form (`AbstractInitTree.leaf`) and
    -- the anonymous-constructor sugar (`.leaf`) — the leading
    -- `.` is stripped before lookup. Compound arguments
    -- (themselves calls / constructors / infix operators / …)
    -- are wrapped in parentheses via the shared `needsParen`
    -- so that nested juxtapositions remain unambiguous.
    let renderArg (e : DslExpr) : MathDoc :=
      let d := go e
      if needsParen e then MathDoc.paren d else d
    let findVariant (short : String) : Option VariantDef :=
      -- The global `resolveVariant` returns the first variant
      -- with a matching short name, which can mis-resolve when
      -- several enums share a constructor name (`deref`,
      -- `downcast`, `index`, …). Prefer a variant whose arity
      -- matches the call's visible arguments; fall back to the
      -- first match only if no arity-matching variant exists.
      let arityMatch :=
        ctx.variants.find? fun v =>
          v.name.name == short &&
          v.args.length == visibleArgs.length
      arityMatch.orElse fun _ => ctx.resolveVariant short
    let ctorCallDoc : Option MathDoc := match fn with
      | .var n =>
        let lookup :=
          if n.startsWith "." then (n.drop 1).toString else n
        match findVariant lookup with
        | some v =>
          if v.args.length == visibleArgs.length then
            let argMap : List (String × DslExpr) :=
              (v.args.map (·.name)).zip visibleArgs
            let resolveArg (name : String) :
                Option (DslExpr × MathDoc) :=
              argMap.find? (·.1 == name) |>.map
                fun (_, e) => (e, go e)
            some (renderDisplayParts v.display resolveArg)
          else none
        | none => none
      | _ => none
    -- A call whose head names a function with a custom
    -- display template renders using that template, with each
    -- `#param` reference replaced by the rendered argument at
    -- the matching positional slot. Falls through to the
    -- default `fn(args)` rendering when no template is found.
    let fnDisplayDoc : Option MathDoc := match fn with
      | .var n =>
        let short := (n.splitOn ".").getLast?.getD n
        match ctx.resolveFnDisplay short with
        | some (parts, paramNames) =>
          if paramNames.length == visibleArgs.length then
            let argMap : List (String × DslExpr) :=
              paramNames.zip visibleArgs
            let resolveArg (name : String) :
                Option (DslExpr × MathDoc) :=
              argMap.find? (·.1 == name) |>.map
                fun (_, e) => (e, go e)
            some (renderDisplayParts parts resolveArg)
          else none
        | none => none
      | _ => none
    -- A call of the form `<ns>.join a b` is rendered as
    -- `a ∪ b` in math mode — for example a call to
    -- `ValidityConditions.join` inside `BorrowsGraph.join`'s
    -- body. Symmetrically, `<ns>.meet a b` renders as
    -- `a ∩ b` — for example a call to `InitialisationState.meet`
    -- inside `InitTree.meet`'s body.
    --
    -- Compound names whose final segment ends in capitalised
    -- `Join` / `Meet` are treated the same way so helpers like
    -- `ownedLocalsMeet xs ys` also render as `xs ∩ ys`.
    let isJoinName (s : String) : Bool :=
      s == "join" || s.endsWith "Join"
    let isMeetName (s : String) : Bool :=
      s == "meet" || s.endsWith "Meet"
    let latticeOpDoc : Option MathDoc := match fn, visibleArgs with
      | .var n, [a, b] =>
        let short := (n.splitOn ".").getLast?.getD n
        if isJoinName short then
          some (.seq [renderArg a, .sym .cup, renderArg b])
        else if isMeetName short then
          some (.seq [renderArg a, .sym .cap, renderArg b])
        else none
      | _, _ => none
    match implicitFnDoc, ctorCallDoc, fnDisplayDoc, latticeOpDoc with
    | some md, _, _, _ => md
    | _, some md, _, _ => md
    | _, _, some md, _ => md
    | _, _, _, some md => md
    | none, none, none, none =>
      let fnDoc := match fn with
        | .var n => fnRef n
        | _ => go fn
      -- Inside a property body, the call rendering follows
      -- `PRESENTATION_PROP_APP_STYLE`; outside, it follows
      -- `PRESENTATION_FN_APP_STYLE`. `Haskell` produces
      -- `f a b` (with `renderArg` parens around compound
      -- args), `Rust` produces `f(a, b)`.
      let style :=
        if isProperty then PRESENTATION_PROP_APP_STYLE
        else PRESENTATION_FN_APP_STYLE
      if style == .Haskell then
        .seq ([fnDoc] ++ visibleArgs.flatMap fun e =>
          [.sym .space, renderArg e])
      else
        .seq [ fnDoc, MathDoc.paren
                 (mathIntercalate (.sym .comma)
                   (visibleArgs.map go)) ]
  | .foldlM fn init list =>
    -- `^*` is a superscript that decorates the function
    -- reference; no backend-independent form yet.
    let fnDoc := match fn with
      | .var n => fnRef n
      | _ => go fn
    .seq [ fnDoc, rawMath "^*"
         , MathDoc.paren
             (.seq [go init, .sym .comma, go list]) ]
  | .lt l r => .seq [go l, .sym .lt, go r]
  | .le l r => .seq [go l, .sym .le, go r]
  | .ineqChain ops es =>
    let docs := es.map go
    let syms := ops.map fun | .lt => MathDoc.sym .lt
                            | .le => MathDoc.sym .le
    match docs with
    | [] => .seq []
    | [d] => d
    | d :: ds =>
      .seq (d :: (syms.zip ds).flatMap
        fun (s, d) => [s, d])
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
  | .forall_ binders b =>
    -- One leading `\forall`, then each group rendered as
    -- `x` / `x ∈ T` / `x y z ∈ T`, separated by `,`. The
    -- binder list is separated from the body by `.`, matching
    -- the DSL surface syntax (`∀∀ … . body`). Type names
    -- render as upright `\text{T}` (matching how named types
    -- appear in `Reachable`-style captions); bound variables
    -- stay italic via `.raw`.
    let renderGroup : List String × Option String → MathDoc :=
      fun (vars, ty) =>
        let varDocs : List MathDoc :=
          vars.map (fun v => .raw v)
            |>.intersperse (.sym .space)
        match ty with
        | none => .seq varDocs
        | some t =>
          .seq (varDocs ++ [.sym .setContains, .text t])
    let groupDocs := binders.map renderGroup
    .seq [.sym .forall_,
          mathIntercalate (.sym .comma) groupDocs,
          rawMath "~.~", go b]
  | .sorryProof => .seq []
  | .leanProof _ => .seq []
  | .match_ scrut arms =>
    -- Pass `ctx.ctorDisplay` so nullary variants in inner
    -- `match` arms render with their display template
    -- (e.g. `PreOperands`), matching how the same variant
    -- renders in value position via `varToVariantDoc`.
    let rowsMath : List MathDoc :=
      arms.map fun (pats, rhs) =>
        let patMath := mathIntercalate (.sym .comma)
          (pats.map (BodyPat.toDoc ctx.ctorDisplay
            ctx.resolveCtor ctx.resolveVariant
            ctx.variants))
        -- Two-column `{ll}` array: pattern in the first
        -- column, `⇒ rhs` in the second, so every row
        -- aligns on the fat arrow. `&` is the LaTeX array
        -- column separator; trailing ` \\` ends the row.
        .seq [ rawMath "  ", patMath
             , rawMath " &", .sym .fatArrow, go rhs
             , rawMath " \\\\" ]
    -- `\left\{\begin{array}{ll}…\end{array}\right.` is a
    -- LaTeX-specific aligned-cases environment; kept raw.
    .seq [ keyword "match", go scrut, .sym .space
         , rawMath "\\left\\{\\begin{array}{ll}\n"
         , mathIntercalate (rawMath "\n") rowsMath
         , rawMath "\n\\end{array}\\right." ]
  | .letIn pat val body =>
    let patDoc := BodyPat.toDoc (fun _ => none)
      ctx.resolveCtor ctx.resolveVariant ctx.variants pat
    .seq [ keyword "let", patDoc, .sym .assign
         , go val, .sym .semicolon, .sym .space, go body ]
  | .letBindIn pat val body =>
    let patDoc := BodyPat.toDoc (fun _ => none)
      ctx.resolveCtor ctx.resolveVariant ctx.variants pat
    .seq [ keyword "let", patDoc, .sym .leftarrow
         , go val, .sym .semicolon, .sym .space, go body ]
  | .ifThenElse c t e =>
    .seq [ keyword "if", go c, .sym .space
         , keyword "then", go t, .sym .space
         , keyword "else", go e ]
  | .neq l r => .seq [go l, .sym .neq, go r]
  | .eq l r => .seq [go l, .sym .eq, go r]
  | .propEq l r => .seq [go l, .sym .eq, go r]
  | .memberOf l r => .seq [go l, .sym .setContains, go r]
  | .anyList list param body =>
    -- `∃ param ∈ list, body` — an existential over a list.
    .seq [.sym .exists_, .raw param, .sym .setContains,
          go list, .sym .comma, go body]
  | .structUpdate recv fieldName newValue =>
    -- `recv[fieldName ↦ newValue]` — same bracket/`\mapsto`
    -- form used for `mapInsert`, since both express
    -- "value of `recv` with one slot replaced".
    .seq [ go recv, MathDoc.bracket
             (.seq [MathDoc.text fieldName, .sym .mapsto,
                    go newValue]) ]
  | .formatHint hint body =>
    -- Emit a math-mode break / indent before the wrapped
    -- body. The Latex-side `seq`-with-breaks lowering lifts
    -- the surrounding sequence into a single-column array
    -- so the break renders as a real line. When the
    -- enclosing renderer disallows breaks (e.g. `inferrule`
    -- conclusions), the wrapper falls back to rendering the
    -- body unchanged.
    if !ctx.allowBreak then go body
    else match hint with
      | .break_ => .seq [.break_, go body]
      | .indent n => .indent n (go body)
      | .breakIndent n => .seq [.break_, .indent n (go body)]

end DslExpr
