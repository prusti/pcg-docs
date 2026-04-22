import Core.Export.Latex
import Core.Dsl.DslType

/-- An argument of an enum variant (e.g. `v : RegionVid`). -/
structure ArgDef where
  /-- The argument name (e.g. `"v"`). -/
  name : String
  /-- The argument type (e.g. `RegionVid`). -/
  type : DSLType
  deriving Repr

/-- A part of a variant's display template. Either a literal
    `MathDoc` fragment or a reference to an argument with its
    own display symbol. Display parts always appear in math
    context. -/
inductive DisplayPart where
  /-- Literal math content. -/
  | lit (d : MathDoc)
  /-- Argument reference with its display symbol.
      E.g. `arg "region" (.var "r")` renders the
      `region` argument as *r*. -/
  | arg (name : String) (symbolDoc : MathDoc)
  deriving Repr

/-- A single variant in an exportable enum definition. -/
structure VariantDef where
  /-- The variant name (e.g. `"exclusive"`). -/
  name : DSLNamedTy
  /-- Documentation for this variant. -/
  doc : Doc
  /-- Display template: a list of literal fragments and
      argument references that together form the
      mathematical notation for this variant. -/
  display : List DisplayPart
  /-- Arguments of this variant (empty for nullary). -/
  args : List ArgDef
  deriving Repr

/-- An exportable enum definition with metadata for cross-language
    code generation and presentation. -/
structure EnumDef where
  /-- The enum name (e.g. `"Capability"`). -/
  name : DSLNamedTy
  /-- Formatted type symbol for document exports. -/
  symbolDoc : MathDoc
  /-- Symbol for the set of all values of this type. -/
  setDoc : MathDoc
  /-- LaTeX definition title (e.g. `"Operands"`). -/
  defnName : String
  /-- Top-level documentation. -/
  doc : Doc
  /-- Implicit type parameters (e.g. `["P"]` for
      `MaybeLabelledPlace {P}`). These render as implicit
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
  /-- The variants of the enum. -/
  variants : List VariantDef
  deriving Repr

namespace DisplayPart

/-- Render a display part as a `Doc` (wraps in math). -/
def toDoc : DisplayPart → Doc
  | .lit d => .math d
  | .arg _ sym => .math sym

end DisplayPart

namespace VariantDef

/-- Render the variant's display template as a `Doc`
    (using the symbolic form of each argument). -/
def displayDoc (v : VariantDef) : Doc :=
  .seq (v.display.map DisplayPart.toDoc)

end VariantDef

namespace EnumDef

/-- Short formal definition: `c ::= E | W | R | e` -/
def shortDef (d : EnumDef) : Doc :=
  let lhs := Doc.math d.symbolDoc
  let rhs := Doc.intercalate (.plain " | ")
    (d.variants.map fun v => v.displayDoc)
  .seq [lhs, .plain " ::= ", rhs]

/-- Long formal definition with descriptions. -/
def longDef (d : EnumDef) : Doc :=
  let header := Doc.seq
    [d.doc, .plain " ", .math d.symbolDoc,
     .plain " is one of:"]
  let items := d.variants.map fun v =>
    Doc.seq [v.displayDoc, .plain ": ", v.doc]
  .seq [header, .line, .itemize items]

end EnumDef

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

/-- Render the variant's display template to `LatexMath`. -/
def displayLatexMath (v : VariantDef) : LatexMath :=
  .seq (v.display.map DisplayPart.toLatexMath)

/-- Like `displayLatexMath`, but renders argument references
    using the argument's declared name rather than its
    auto-looked-up `symbolDoc`. Used for the long form, where
    the subsequent `where`-block binds each name explicitly. -/
def displayLatexMathNamed (v : VariantDef) : LatexMath :=
  .seq (v.display.map fun
    | .lit d => d.toLatexMath
    | .arg name _ => .escaped name)

/-- Render the variant's display template as a `MathDoc`
    (using the symbolic form of each argument). -/
def displayMathDoc (v : VariantDef) : MathDoc :=
  .seq (v.display.map fun
    | .lit d => d
    | .arg _ sym => sym)

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
    match v.args with
    | [] => [headerRow]
    | args => headerRow :: whereRow :: args.map argRow

/-- Render the enum as a LaTeX `definition` environment.

    The body of the definition is a `sym ∈ Set ::= …` display
    where the right-hand side uses either the short `A | B | C`
    form or — when `d.longDef` is set — the long form that
    also lists each variant's arguments in `where`-block
    style. The prose description preceding the environment is
    the same in both cases. -/
def formalDefLatex (d : EnumDef)
    (knownTypes : String → Bool := fun _ => false) : Latex :=
  let sym := d.symbolDoc.toLatexMath
  let rows : List (List LatexMath) :=
    if d.useLongForm then longRows d knownTypes
    else shortRows d
  -- Invisible hypertarget so cross-references to this type
  -- (e.g. from function signatures) can link here via
  -- `\hyperlink{type:<name>}{...}`.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{d.name.name}}\{}"
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
