import Core.Export.Latex
import Core.Dsl.DslType
import Core.Dsl.Types.Feature

/-- An argument of an enum variant (e.g. `v : RegionVid`). -/
structure ArgDef where
  /-- The argument name (e.g. `"v"`). -/
  name : String
  /-- The argument type (e.g. `RegionVid`). -/
  type : DSLType
  /-- The argument's auto-looked-up `MathDoc` symbol (the
      registered `symbolDoc` of its type, or
      `MathDoc.text "<name>"` for primitive containers /
      type-parameter slots that have no registered symbol).
      Used as the default substitution for the matching
      argument slot in `VariantDef.display`. -/
  symbolDoc : MathDoc
  deriving Repr

/-- A part of a variant's display template. Either a literal
    `MathDoc` fragment or a reference to an argument with its
    own display symbol. Display parts always appear in math
    context. Retained for use by `defStruct` / `defFn` /
    `defProperty` display templates; `defEnum` variants now
    use the more flexible `MathDoc`-valued display function
    on `VariantDef.display`. -/
inductive DisplayPart where
  /-- Literal math content. -/
  | lit (d : MathDoc)
  /-- Argument reference with its display symbol.
      E.g. `arg "region" (.var "r")` renders the
      `region` argument as *r*. -/
  | arg (name : String) (symbolDoc : MathDoc)
  deriving Repr

/-- The `Repr` instance is a stub: the function value carried
    by `VariantDef.display` is opaque. The instance exists so
    `EnumDef` (which contains `List VariantDef`) can continue
    to derive `Repr`; only debug-printing of `EnumDef`s would
    notice the placeholder, and no production code does that. -/
instance : Repr (List MathDoc → MathDoc) :=
  ⟨fun _ _ => Std.Format.text "<displayFn>"⟩

/-- A single variant in an exportable enum definition. -/
structure VariantDef where
  /-- The variant name (e.g. `"exclusive"`). -/
  name : DSLIdent
  /-- Documentation for this variant. -/
  doc : Doc
  /-- Display template as a function from per-argument
      `MathDoc` values (positional, matching `args`) to a
      `MathDoc` rendering. The `defEnum` elaborator builds
      this by wrapping the user-written display expression
      in a function over the variant's arguments — a free
      identifier `idx` inside the user expression resolves to
      the bound `idx : MathDoc` parameter at rendering time,
      and callers (default rendering, named-form rendering,
      `DslExpr` call-site substitution) supply different
      argument lists to drive the matching MathDoc output. -/
  display : List MathDoc → MathDoc
  /-- Arguments of this variant (empty for nullary). -/
  args : List ArgDef
  /-- Feature flags this variant is gated on. The LaTeX
      presentation omits the variant when any feature in this
      list is disabled in the current presentation. Empty (the
      default) means always rendered. The Lean and Rust
      exports ignore this field — they always emit every
      variant. -/
  features : List Feature := []
  deriving Repr

/-- An exportable enum definition with metadata for cross-language
    code generation and presentation. -/
structure EnumDef where
  /-- The enum name (e.g. `"Capability"`). -/
  name : DSLIdent
  /-- Formatted type symbol for document exports. -/
  symbolDoc : MathDoc
  /-- Symbol for the set of all values of this type. -/
  setDoc : MathDoc
  /-- LaTeX definition title (e.g. `"Operands"`). -/
  defnName : String
  /-- Top-level documentation. -/
  doc : Doc
  /-- Implicit type parameters (e.g. `["P"]` for
      `MaybeLabelled {P}`). These render as implicit
      type parameters in Lean and as generics in Rust. -/
  typeParams : List String := []
  /-- When true, the formal LaTeX definition renders each
      variant with an explicit `where` sub-block listing
      its arguments (name and type), in the style of a
      struct's where-block. When false (the default), the
      short `c ::= A | B | C` form is used. This affects
      only the math portion of the definition; the prose
      description is unchanged either way. -/
  useLongForm : Bool := false
  /-- When `true`, the LaTeX presentation attaches the
      type parameters as a subscript to `symbolDoc` in the
      formal definition (e.g. `rg_D` instead of `rg` for
      `RequiredGuide {D}`). Defaults to `false` so existing
      definitions are unaffected; opt in by passing
      `subscript` in the DSL. -/
  subscriptTypeParams : Bool := false
  /-- The variants of the enum. -/
  variants : List VariantDef
  deriving Repr

mutual

/-- Convert a `Doc` (typically produced by `doc! "$...$"`)
    into a list of `DisplayPart`s for use as a `displayed`
    template. Each `MathDoc.text name` (which is what `doc!`
    emits for `#name` references inside a `$...$` block) is
    classified as either a parameter slot — when `name`
    matches a registered parameter — or as a literal piece
    of math text. Every other `MathDoc` and outer-`Doc`
    fragment becomes a literal display part, so non-math
    prose surrounding the math block flows through the same
    template. -/
partial def Doc.toDisplayParts
    (paramNames : List String) :
    Doc → List DisplayPart
  | .math md => MathDoc.toDisplayParts paramNames md
  | .seq ds => ds.flatMap (Doc.toDisplayParts paramNames)
  | .plain s =>
    if s.isEmpty then [] else [.lit (.doc (.plain s))]
  | d => [.lit (.doc d)]

partial def MathDoc.toDisplayParts
    (paramNames : List String) :
    MathDoc → List DisplayPart
  -- A `MathDoc.text name` (= `MathDoc.doc (Doc.plain name)`)
  -- whose name matches a registered parameter is reclassified
  -- as a parameter slot. The fallback symbol doc is set to an
  -- empty `MathDoc.raw` since the inductive-property header
  -- renderer ignores it, and call-site rendering substitutes
  -- the actual argument.
  | .doc (.plain s) =>
    if paramNames.contains s then
      [.arg s (.raw "")]
    else
      [.lit (.doc (.plain s))]
  | .seq mds => mds.flatMap (MathDoc.toDisplayParts paramNames)
  | md => [.lit md]

end

namespace VariantDef

/-- Apply the variant's display function with each argument
    bound to its auto-looked-up `symbolDoc`. -/
def displayMathDoc (v : VariantDef) : MathDoc :=
  v.display (v.args.map (·.symbolDoc))

/-- Render the variant's display as a `Doc`. -/
def displayDoc (v : VariantDef) : Doc :=
  .math v.displayMathDoc

end VariantDef

-- ══════════════════════════════════════════════
-- LaTeX rendering
-- ══════════════════════════════════════════════

namespace DisplayPart

/-- Render a display part to `LatexMath`. -/
def toLatexMath : DisplayPart → LatexMath
  | .lit d => MathDoc.toLatexMath d
  | .arg _ sym => MathDoc.toLatexMath sym

end DisplayPart

namespace VariantDef

/-- Render the variant's display template to `LatexMath`,
    with each argument substituted by its auto-looked-up
    `symbolDoc`. -/
def displayLatexMath (v : VariantDef) : LatexMath :=
  v.displayMathDoc.toLatexMath

/-- Like `displayLatexMath`, but renders argument references
    using the argument's declared name rather than its
    auto-looked-up `symbolDoc`. Used for the long form, where
    the subsequent `where`-block binds each name explicitly. -/
def displayLatexMathNamed (v : VariantDef) : LatexMath :=
  (v.display (v.args.map fun a => MathDoc.text a.name)).toLatexMath

end VariantDef

namespace EnumDef

/-- Rows for the short (default) math body: one row per
    variant, each row `| variantDisplay (variantDoc)`. -/
private def shortRows (d : EnumDef) : List (List LatexMath) :=
  d.variants.zipIdx.map fun (v, i) =>
    let sep : LatexMath :=
      if i == 0 then .raw "  "
      else .cmd "mid"
    -- Place an invisible hypertarget so cross-references
    -- (e.g. `Value.int`, `AbstractByte.init`) can link
    -- here via `\hyperlink{ctor:<EnumName>.<variantName>}{...}`.
    -- The fully-qualified anchor prevents collisions between
    -- variants with the same short name across different enums.
    let target : LatexMath :=
      .raw s!"\\hypertarget\{ctor:{d.name.name}.{v.name.name}}\{}"
    let variant : LatexMath :=
      .seq [.raw " ", target, v.displayLatexMath]
    let desc : LatexMath :=
      .seq [.raw "~", .text (Latex.parbox
        "\\dimexpr\\linewidth-8cm\\relax" (.seq [
          .raw "(", v.doc.toLatex, .raw ")"]))]
    [sep, variant, desc]

/-- Rows for the long math body: each variant still gets
    a `| variantDisplay (variantDoc)` row, but variants with
    arguments follow it with one row per argument listing
    `argName : argType`, mirroring the `where`-block of a
    struct definition. -/
private def longRows
    (d : EnumDef) (knownTypes : String → Bool) :
    List (List LatexMath) :=
  d.variants.zipIdx.flatMap fun (v, i) =>
    let sep : LatexMath :=
      if i == 0 then .raw "  "
      else .cmd "mid"
    let target : LatexMath :=
      .raw s!"\\hypertarget\{ctor:{d.name.name}.{v.name.name}}\{}"
    -- In the long form the variant row renders each argument
    -- reference as the argument's declared name; the subsequent
    -- `where` rows then bind those names to their types.
    let variant : LatexMath :=
      .seq [.raw " ", target, v.displayLatexMathNamed]
    let desc : LatexMath :=
      .seq [.raw "~", .text (Latex.parbox
        "\\dimexpr\\linewidth-8cm\\relax" (.seq [
          .raw "(", v.doc.toLatex, .raw ")"]))]
    let headerRow : List LatexMath := [sep, variant, desc]
    -- The `where` keyword and argument rows go in the array's
    -- second column (aligned with the variant display above),
    -- with a `\quad` indent so `where` sits slightly in from
    -- the variant and each `argName : argType` sits further
    -- in from `where`.
    let whereRow : List LatexMath :=
      [.raw "", .seq [.raw "\\quad ", .text (.text "where")],
       .raw ""]
    let argRow (a : ArgDef) : List LatexMath :=
      let sig : LatexMath := .seq [
        .raw "\\quad\\quad ",
        .escaped a.name, .raw " : ",
        a.type.toLatexMath knownTypes]
      [.raw "", sig, .raw ""]
    -- Drop arguments whose type only references the enum's
    -- own type parameters (e.g. `d : D` in
    -- `AbstractInitTree {D}`). The variant header already
    -- shows the name; repeating the type in the `where`
    -- block would add noise without new information. If all
    -- arguments drop out, omit the whole `where` clause.
    let shownArgs : List ArgDef :=
      v.args.filter fun a => !a.type.onlyUsesParams d.typeParams
    match shownArgs with
    | [] => [headerRow]
    | args => headerRow :: whereRow :: args.map argRow

/-- Render the enum's symbol for the formal definition,
    adding a `_{T₁ T₂ …}` subscript listing the type
    parameters when `subscriptTypeParams` is set. -/
def formalSymbolLatexMath (d : EnumDef) : LatexMath :=
  let base := d.symbolDoc.toLatexMath
  if d.subscriptTypeParams && !d.typeParams.isEmpty then
    let subscript : LatexMath :=
      LatexMath.intercalate (.raw "~")
        (d.typeParams.map LatexMath.var)
    .sub base subscript
  else base

/-- Render the enum as a LaTeX `definition` environment.

    The body of the definition is a `sym ∈ Set ::= …` display
    where the right-hand side uses either the short `A | B | C`
    form or — when `d.longDef` is set — the long form that
    also lists each variant's arguments in `where`-block
    style. The prose description preceding the environment is
    the same in both cases.

    Variants whose `features` list contains a feature disabled
    in the current presentation are filtered out before
    rendering. The Lean and Rust exports walk `d.variants`
    directly elsewhere, so feature flags are presentation-only. -/
def formalDefLatex (d : EnumDef)
    (knownTypes : String → Bool := fun _ => false)
    (isFeatureDisabled : Feature → Bool := fun _ => false)
    : Latex :=
  let visible : EnumDef :=
    { d with variants := d.variants.filter fun v =>
        !v.features.any isFeatureDisabled }
  let sym := visible.formalSymbolLatexMath
  let rows : List (List LatexMath) :=
    if visible.useLongForm then longRows visible knownTypes
    else shortRows visible
  -- Invisible hypertargets so cross-references to this type
  -- (e.g. from function signatures, or via the `doc!` macro's
  -- `#X` shorthand which resolves to `fn:X`) can link here via
  -- `\hyperlink{type:<name>}{...}` or `\hyperlink{fn:<name>}{...}`.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{d.name.name}}\{}\
            \\hypertarget\{fn:{d.name.name}}\{}"
  let typeParamsLM : LatexMath :=
    .seq (d.typeParams.flatMap fun p =>
      [.raw "~", .var p])
  let setDisplay : LatexMath :=
    .seq [d.setDoc.toLatexMath, typeParamsLM]
  .seq [
    d.doc.toLatex, .newline,
    .envOpts "definition" (.text d.defnName) (.seq [
      typeTarget,
      .displayMath (.seq [
        sym, .raw " ", .cmd "in", .raw " ",
        setDisplay, .raw " ::= ",
        .array (some "t") "rll" rows
      ]), .newline
    ])
  ]

end EnumDef
