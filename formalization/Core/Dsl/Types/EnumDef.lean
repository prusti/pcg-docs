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

/-- Render the variant's display template as a `MathDoc`
    (using the symbolic form of each argument). -/
def displayMathDoc (v : VariantDef) : MathDoc :=
  .seq (v.display.map fun
    | .lit d => d
    | .arg _ sym => sym)

end VariantDef

namespace EnumDef

/-- Render the enum as a LaTeX `definition` environment. -/
def formalDefLatex (d : EnumDef) : Latex :=
  let sym := d.symbolDoc.toLatexMath
  let rows := d.variants.zipIdx.map fun (v, i) =>
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
    -- Wrap the description in a `\parbox` so long descriptions
    -- wrap onto multiple lines instead of overflowing the
    -- array row. The width is `\linewidth - 8cm` so the box
    -- adapts to the remaining horizontal space after the
    -- first two columns.
    let desc : LatexMath :=
      .seq [.raw "~", .text (Latex.parbox
        "\\dimexpr\\linewidth-8cm\\relax" (.seq [
          .raw "(", v.doc.toLatex, .raw ")"]))]
    [sep, variant, desc]
  -- Invisible hypertarget so cross-references to this type
  -- (e.g. from function signatures) can link here via
  -- `\hyperlink{type:<name>}{...}`.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{d.name.name}}\{}"
  .envOpts "definition" (.text d.defnName) (.seq [
    typeTarget,
    d.doc.toLatex, .newline,
    .displayMath (.seq [
      sym, .raw " ", .cmd "in", .raw " ",
      d.setDoc.toLatexMath, .raw " ::= ",
      .array (some "t") "rll" rows
    ]), .newline
  ])

end EnumDef
