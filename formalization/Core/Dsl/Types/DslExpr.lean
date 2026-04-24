import Core.Export.Latex
import Core.Dsl.DeriveQuote
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
  | letIn (name : VarIdent) (val : DslExpr) (body : DslExpr)
  /-- `let name ← val ; body` (monadic bind on Option). -/
  | letBindIn (name : String) (val : DslExpr) (body : DslExpr)
  /-- `if cond then t else e`. -/
  | ifThenElse (cond : DslExpr) (t : DslExpr) (e : DslExpr)
  /-- Inequality: `lhs ≠ rhs`. -/
  | neq (lhs : DslExpr) (rhs : DslExpr)
  /-- Equality: `lhs == rhs`. -/
  | eq (lhs : DslExpr) (rhs : DslExpr)
  /-- List existential: `list.any fun param => body`. -/
  | anyList (list : DslExpr) (param : String)
      (body : DslExpr)
  /-- Set/List membership: `elem ∈ col`. -/
  | memberOf (elem : DslExpr) (col : DslExpr)
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
  | .forall_ p b => .forall_ p (f b)
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
  | .memberOf l r => .memberOf (f l) (f r)
  -- Ternary (with String parameter)
  | .anyList l p b => .anyList (f l) p (f b)
  | .setAll s p b => .setAll (f s) p (f b)
  | .setFlatMap l p b => .setFlatMap (f l) p (f b)
  | .letIn n v b => .letIn n (f v) (f b)
  | .letBindIn n v b => .letBindIn n (f v) (f b)
  | .ifThenElse c t e => .ifThenElse (f c) (f t) (f e)
  | .foldlM fn init list => .foldlM (f fn) (f init) (f list)
  -- List children
  | .mkStruct n args => .mkStruct n (args.map f)
  | .call fn args => .call (f fn) (args.map f)
  | .ineqChain ops es => .ineqChain ops (es.map f)
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
    --      `join` inside `PCG.Owned.InitTree` resolves to
    --      `#fn:InitTree.join`. This is the best-effort
    --      resolution for unqualified ambiguous calls.
    --  (4) Otherwise fall back to a constructor reference.
    let shortName := (fn.splitOn ".").getLast?.getD fn
    let mkLink (target : String) : MathDoc :=
      .doc (.link (.plain (Doc.fnNameDisplay fn))
        s!"#fn:{target}")
    if fn != shortName && ctx.knownFnAnchors fn then
      mkLink fn
    else if ctx.knownFns shortName && !ctx.ambiguousFns shortName then
      mkLink shortName
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
    .seq [MathDoc.text "Some", MathDoc.paren (go e)]
  | .mkStruct name args =>
    let argDocs := args.map go
    if name == "" then
      -- Anonymous tuple literal: use angle brackets so it
      -- visually differs from a function-call argument list.
      .seq [ .sym .langle
           , mathIntercalate (.sym .comma) argDocs
           , .sym .rangle ]
    else
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
    .seq [fnRef method, MathDoc.paren (go recv)]
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
    -- Drop proof arguments: they render as empty math
    -- and would otherwise leave a trailing comma.
    let visibleArgs := args.filter fun
      | .sorryProof => false
      | .leanProof _ => false
      | _ => true
    -- A call whose head names a known enum variant renders
    -- using the variant's display template, with each arg
    -- reference replaced by the rendered argument. This
    -- produces the natural `leaf cap` / `internal (fields fs)`
    -- form instead of the Lean-source `.leaf(cap)`. Accepts
    -- both the qualified form (`AbstractInitTree.leaf`) and
    -- the anonymous-constructor sugar (`.leaf`) — the leading
    -- `.` is stripped before lookup. Compound arguments
    -- (themselves calls / constructors / cons chains) are
    -- wrapped in parentheses so that nested juxtapositions
    -- remain unambiguous.
    let needsParen : DslExpr → Bool
      | .call .. => true
      | .mkStruct name _ => name != ""
      | .cons .. => false
      | .some_ _ => true
      | _ => false
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
            let parts : List MathDoc := v.display.map fun
              | .lit d => d
              | .arg name _ =>
                match argMap.find? (·.1 == name) with
                | some (_, e) => renderArg e
                | none => MathDoc.text name
            some (MathDoc.seq parts)
          else none
        | none => none
      | _ => none
    -- A call of the form `<ns>.join a b` is rendered as
    -- `a ∪ b` in math mode — for example a call to
    -- `InitialisationState.join` inside `InitTree.join`'s
    -- body, or a call to `ValidityConditions.join` inside
    -- `BorrowsGraph.join`'s body.
    let joinCupDoc : Option MathDoc := match fn, visibleArgs with
      | .var n, [a, b] =>
        let short := (n.splitOn ".").getLast?.getD n
        if short == "join" then
          some (.seq [renderArg a, .sym .cup, renderArg b])
        else none
      | _, _ => none
    match ctorCallDoc, joinCupDoc with
    | some md, _ => md
    | _, some md => md
    | none, none =>
      let fnDoc := match fn with
        | .var n => fnRef n
        | _ => go fn
      if isProperty then
        -- Inside an inductive-property rule, render calls in
        -- prefix-application style with space-separated
        -- arguments (e.g. `HasNonDeepLeaf d`) — matching the
        -- way propositions are typeset on paper. Compound
        -- arguments are still parenthesised by `renderArg`,
        -- so `HasNonDeepLeaf (leaf cap)` stays unambiguous.
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
          (pats.map (BodyPat.toDoc noCtor
            ctx.resolveCtor ctx.resolveVariant))
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
  | .letIn name val body =>
    .seq [ keyword "let", .raw name.name, .sym .assign
         , go val, .sym .semicolon, .sym .space, go body ]
  | .letBindIn name val body =>
    .seq [ keyword "let", .raw name, .sym .leftarrow
         , go val, .sym .semicolon, .sym .space, go body ]
  | .ifThenElse c t e =>
    .seq [ keyword "if", go c, .sym .space
         , keyword "then", go t, .sym .space
         , keyword "else", go e ]
  | .neq l r => .seq [go l, .sym .neq, go r]
  | .eq l r => .seq [go l, .sym .eq, go r]
  | .memberOf l r => .seq [go l, .sym .setContains, go r]
  | .anyList list param body =>
    -- `∃ param ∈ list, body` — an existential over a list.
    .seq [.sym .exists_, .raw param, .sym .setContains,
          go list, .sym .comma, go body]

end DslExpr
