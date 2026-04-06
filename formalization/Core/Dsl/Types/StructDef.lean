import Core.Export.Latex
import Core.Dsl.DslType

/-- A field of an exportable struct definition. -/
structure FieldDef where
  /-- The field name (e.g. `"id"`). -/
  name : String
  /-- The field type. -/
  ty : DSLType
  /-- Documentation for this field. -/
  doc : String
  deriving Repr

/-- An exportable struct definition with metadata for
    cross-language code generation. -/
structure StructDef where
  /-- The struct name (e.g. `"RegionVid"`). -/
  name : String
  /-- Formatted type symbol for document exports. -/
  symbolDoc : MathDoc
  /-- Symbol for the set of all values of this type. -/
  setDoc : MathDoc
  /-- LaTeX definition title (e.g. `"Basic Blocks"`). -/
  docParam : String
  /-- Top-level documentation. May contain inline math
      from `{def}` interpolation. -/
  doc : Doc
  /-- Optional constructor name (e.g. `"LocalIdx"`).
      When set, renders as `sym ∈ set ::= Ctor(params)`.
      When `none`, renders with angle brackets. -/
  ctorName : Option String := none
  /-- The fields of the struct. -/
  fields : List FieldDef
  deriving Repr

namespace StructDef

/-- Render the struct as a LaTeX `definition` environment. -/
def formalDefLatex (s : StructDef) : Latex :=
  let sym := s.symbolDoc.toLatexMath
  let sp := MathSym.space.toLatex
  let fieldNames : LatexMath :=
    .seq (s.fields.map fun f =>
      .seq [sp, .escaped f.name])
  let typedParams : LatexMath :=
    LatexMath.intercalate (.raw ",~")
      (s.fields.map fun f =>
        .seq [.escaped f.name, .raw " : ",
              (f.ty.toDoc .math).toLatexMath])
  let rhs : LatexMath := match s.ctorName with
    | some name =>
      .seq [.texttt name, fieldNames]
    | none =>
      .delimited "\\langle " "\\rangle" typedParams
  let defLine : Latex :=
    if s.fields.isEmpty then .seq []
    else .seq [
      .newline,
      .displayMath (.seq [
        sym, .raw " ", .cmd "in", .raw " ",
        s.setDoc.toLatexMath, .raw " ::= ", rhs]),
      .newline]
  let whereBlock : Latex :=
    if s.fields.isEmpty then .seq []
    else
      let fieldRows := s.fields.map fun f =>
        [ .escaped f.name
        , .seq [.raw ": ",
                (f.ty.toDoc .math).toLatexMath]
        , .seq [.raw " ", .text (.text s!"({f.doc})")]
        ]
      .seq [.raw "where", .newline,
            .displayMath (.array none "rll" fieldRows),
            .newline]
  .envOpts "definition" s.docParam (.seq [
    s.doc.toLatex,
    defLine,
    whereBlock
  ])

end StructDef
