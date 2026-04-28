import Core.Export.Latex
import Core.Dsl.DeriveQuote
import Core.Dsl.Types.EnumDef

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
  deriving Repr, Inhabited, Lean.Quote

-- ══════════════════════════════════════════════
-- Doc rendering
-- ══════════════════════════════════════════════

/-- Intercalate a separator between math doc fragments. -/
def mathIntercalate (sep : MathDoc)
    : List MathDoc → MathDoc
  | [] => .seq []
  | [m] => m
  | ms => .seq (ms.intersperse sep)

namespace BodyPat

/-- Render a constructor name as a hyperlinked reference when it
    resolves to a known variant. Accepts either short (`int`) or
    qualified (`Value.int`) forms; the anchor always uses the
    fully-qualified form (e.g. `ctor:Value.int`) so that variants
    with the same short name in different enums do not collide.
    The grey dashed-underline style is applied automatically by
    the LaTeX backend for any `#`-prefixed URL — see
    `Latex.internalLink`. -/
def ctorRef
    (resolveCtor : String → Option String) (n : String) : MathDoc :=
  -- A leading `.` is the anonymous-constructor sugar that the
  -- DSL preserves in names (e.g. `.leaf`); strip it before
  -- looking up the qualified form.
  let lookupName :=
    if n.startsWith "." then (n.drop 1).toString else n
  match resolveCtor lookupName with
  | some qualified =>
    .doc (.link (.plain n) s!"#ctor:{qualified}")
  | none => MathDoc.text n

/-- Strip a leading `.` (the anonymous-constructor sugar
    sometimes preserved in pattern names) so that lookups
    use the bare short name. -/
private def stripDot (n : String) : String :=
  if n.startsWith "." then (n.drop 1).toString else n

/-- Resolve a constructor short or qualified name to its
    `VariantDef`, treating `(name, arity)` as the
    fully-qualified identifier of the variant. Arity
    disambiguates between variants that share a short name
    across enums but differ in their argument count
    (e.g. `ProjElem.deref` is nullary while `PcgEdge.deref`
    takes one argument).

    Resolution order:
    1. Trust the caller-supplied `resolveVariant` whenever
       it returns a variant whose arity matches the pattern
       — this preserves scoped lookups from
       `FnDef.scopedResolveVariant`, which prefers a variant
       under the scrutinee parameter's type namespace.
    2. Otherwise pick the first variant in `variants` whose
       short name and arity both match — useful for inner
       `match` expressions where the scrutinee's type isn't
       available.
    3. Fall back to whatever `resolveVariant` returned (or
       `none` if it returned nothing). -/
private def lookupVariant
    (variants : List VariantDef)
    (resolveVariant : String → Option VariantDef)
    (n : String) (arity : Nat) : Option VariantDef :=
  let short := stripDot n
  let viaResolver := resolveVariant n
  let resolverArityMatch :=
    viaResolver.filter (·.args.length == arity)
  let arityMatch := variants.find? fun v =>
    v.name.name == short && v.args.length == arity
  match resolverArityMatch with
  | some v => some v
  | none =>
    match arityMatch with
    | some v => some v
    | none => viaResolver

/-- Strip the anonymous-constructor `.` prefix or the
    `Option.` qualifier from a constructor name, returning
    the bare short name. Used to detect `Option`'s
    `some`/`none` constructors regardless of how they were
    written in the source pattern. -/
private def stripOptionQualifier (n : String) : String :=
  if n.startsWith "." then (n.drop 1).toString
  else if n.startsWith "Option." then (n.drop 7).toString
  else n

/-- Whether a pattern needs to be parenthesised when placed in
    a juxtaposition position (e.g. as the argument of `Some` or
    of a unary defEnum constructor's display template). Atomic
    shapes — wildcards, variables, numeric literals, anonymous
    tuples, list literals, nullary constructors — render without
    surrounding delimiters and don't need parens; everything
    else (a constructor applied to arguments, a non-list-literal
    cons chain) does. -/
private partial def needsParen : BodyPat → Bool
  | .wild | .var _ | .natLit _ | .nil => false
  | .ctor "⟨⟩" _ => false
  | .ctor _ as => !as.isEmpty
  | .cons h t =>
    -- A cons chain that bottoms out in `.nil` renders as a
    -- bracketed list literal `[a, b, c]` (atomic). Otherwise
    -- the chain renders with infix `::` and needs parens.
    let rec endsInNil : BodyPat → Bool
      | .nil => true
      | .cons _ t => endsInNil t
      | _ => false
    !(endsInNil (.cons h t))

partial def toDoc
    (ctorDisplay : String → Option MathDoc)
    (resolveCtor : String → Option String := fun _ => none)
    (resolveVariant : String → Option VariantDef :=
      fun _ => none)
    (variants : List VariantDef := [])
    : BodyPat → MathDoc
  | .wild => .sym .underscore
  | .var n => .raw n
  | .ctor "⟨⟩" args =>
    .seq [ .sym .langle
         , mathIntercalate (.sym .comma)
             (args.map (toDoc ctorDisplay
               resolveCtor resolveVariant variants))
         , .sym .rangle ]
  | .ctor n args =>
    -- `Option`'s `some`/`none` are not registered as a
    -- defEnum, so they would otherwise fall through to the
    -- unknown-ctor branch below and render as
    -- `\text{some}(x)` / `\text{none}` — lowercase, with
    -- function-call parens around the argument. Special-case
    -- them here so they render as `Some x` / `None`,
    -- matching the explicit `Some`/`None` expression syntax
    -- and the space-juxtaposition style used by other
    -- defEnum constructors.
    let optionCtor : Option (String × Bool) :=
      match stripOptionQualifier n with
      | "none" | "None" => some ("None", false)
      | "some" | "Some" => some ("Some", true)
      | _ => none
    let renderInJuxtaposition (p : BodyPat) : MathDoc :=
      let inner := toDoc ctorDisplay resolveCtor resolveVariant
        variants p
      if needsParen p then MathDoc.paren inner else inner
    match optionCtor, args with
    | some ("None", _), [] => MathDoc.text "None"
    | some ("Some", _), [arg] =>
      .seq [MathDoc.text "Some", .sym .space,
            renderInJuxtaposition arg]
    | _, _ =>
      if args.isEmpty then
        -- Nullary patterns use the caller-supplied
        -- `ctorDisplay` (the registry-wide variant→display
        -- map at top-level patterns, or `none` for inner
        -- matches that prefer a linked bare name). No arity
        -- disambiguation is needed: a nullary pattern
        -- already encodes its own arity (0).
        match ctorDisplay n with
        | some display => display
        | none => ctorRef resolveCtor n
      else
        -- Non-nullary patterns: resolve the variant via
        -- arity-aware lookup so that patterns like
        -- `.deref de` (1 arg) resolve to the unique
        -- arity-1 variant (`PcgEdge.deref`,
        -- `PlaceExpansion.deref`, …) rather than the
        -- nullary `ProjElem.deref`. The pair
        -- `(short name, arity)` acts as the
        -- fully-qualified identifier of the variant.
        match lookupVariant variants resolveVariant n args.length with
        | some v =>
          let argMap : List (String × BodyPat) :=
            (v.args.map (·.name)).zip args
          let parts : List MathDoc := v.display.map fun
            | .lit d => d
            | .arg name _ =>
              match argMap.find? (·.1 == name) with
              | some (_, p) => renderInJuxtaposition p
              | none => MathDoc.text name
          .seq parts
        | none =>
          let argParts :=
            args.map (toDoc ctorDisplay resolveCtor
              resolveVariant variants)
          .seq [ ctorRef resolveCtor n
               , MathDoc.paren
                   (mathIntercalate (.sym .comma) argParts) ]
  | .nil => MathDoc.bracket (.seq [])
  | .cons h t =>
    let rec flatten : BodyPat → Option (List BodyPat)
      | .nil => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      MathDoc.bracket (mathIntercalate (.sym .comma)
        (elems.map (toDoc ctorDisplay resolveCtor
          resolveVariant variants)))
    | none =>
      .seq [ h.toDoc ctorDisplay resolveCtor resolveVariant
               variants
           , .sym .cons
           , t.toDoc ctorDisplay resolveCtor resolveVariant
               variants ]
  | .natLit n => .raw (toString n)

end BodyPat
