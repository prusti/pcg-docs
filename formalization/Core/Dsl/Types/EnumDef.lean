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
  doc : String
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
  /-- Top-level documentation. May contain inline math
      from `{def}` interpolation. -/
  doc : Doc
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
    Doc.seq [v.displayDoc, .plain s!": {v.doc}"]
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
    -- here via `\hyperlink{ctor:<variantName>}{...}`.
    let target : LatexMath :=
      .raw s!"\\hypertarget\{ctor:{v.name.name}}\{}"
    let variant : LatexMath :=
      .seq [.raw " ", target, v.displayLatexMath]
    let desc : LatexMath :=
      .seq [.raw " ", .text (.seq [
        .raw "(", .text v.doc, .raw ")"])]
    [sep, variant, desc]
  -- Invisible hypertarget so cross-references to this type
  -- (e.g. from function signatures) can link here via
  -- `\hyperlink{type:<name>}{...}`.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{d.name.name}}\{}"
  .envOpts "definition" d.defnName (.seq [
    typeTarget,
    d.doc.toLatex, .newline,
    .displayMath (.seq [
      sym, .raw " ", .cmd "in", .raw " ",
      d.setDoc.toLatexMath, .raw " ::= ",
      .array (some "t") "rll" rows
    ]), .newline
  ])

end EnumDef
