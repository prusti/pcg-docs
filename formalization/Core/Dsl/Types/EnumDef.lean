import Core.Doc
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
  symbolDoc : Doc
  /-- Top-level documentation. -/
  doc : String
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
  let lhs := d.symbolDoc
  let rhs := Doc.intercalate (.text " | ")
    (d.variants.map fun v => v.displayDoc)
  .seq [lhs, .text " ::= ", rhs]

/-- Long formal definition with descriptions. -/
def longDef (d : EnumDef) : Doc :=
  let header := Doc.seq
    [.text d.doc, .text " ", d.symbolDoc,
     .text " is one of:"]
  let items := d.variants.map fun v =>
    Doc.seq [v.displayDoc, .text s!": {v.doc}"]
  .seq [header, .line, .itemize items]

end EnumDef

-- ══════════════════════════════════════════════
-- LaTeX rendering
-- ══════════════════════════════════════════════

namespace DisplayPart

/-- Render a display part to LaTeX math mode. -/
def toLatexMath : DisplayPart → String
  | .lit d => Doc.mathToLatexMath d
  | .arg _ sym => Doc.mathToLatexMath sym

end DisplayPart

namespace VariantDef

/-- Render the variant's display template to LaTeX math. -/
def displayLatexMath (v : VariantDef) : String :=
  String.join (v.display.map DisplayPart.toLatexMath)

end VariantDef

namespace EnumDef

/-- Render the enum as a LaTeX `definition` environment with
    an aligned `array` using the display templates. -/
def formalDefLatex (d : EnumDef) : String :=
  let lb := "{"
  let rb := "}"
  let sym := d.symbolDoc.toLatexMath
  let rows := d.variants.zipIdx.map fun (v, i) =>
    let sep := if i == 0 then "  " else "\\mid"
    let variant := v.displayLatexMath
    let desc := Doc.escapeLatex v.doc
    s!"  {sep} & {variant} & \
       \\text{lb}({desc}){rb} \\\\"
  let arrayBody := "\n".intercalate rows
  s!"\\begin{lb}definition{rb}[{d.name.name}]\n\
     {Doc.escapeLatex d.doc}\n\
     \\[ {sym} ::= \\begin{lb}array{rb}[t]\
     {lb}rll{rb}\n\
     {arrayBody}\n\
     \\end{lb}array{rb} \\]\n\
     \\end{lb}definition{rb}"

end EnumDef
