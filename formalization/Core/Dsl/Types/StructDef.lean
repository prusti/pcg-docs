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
  symbolDoc : Doc
  /-- LaTeX definition title (e.g. `"Basic Blocks"`). -/
  docParam : String
  /-- Top-level documentation. -/
  doc : String
  /-- The fields of the struct. -/
  fields : List FieldDef
  deriving Repr

namespace StructDef

/-- Render the struct as a LaTeX `definition` environment. -/
def formalDefLatex (s : StructDef) : Latex :=
  let fieldRows := s.fields.map fun f =>
    [ .escaped f.name
    , .seq [.raw ": ", (f.ty.toDoc .math).toLatexMath]
    , .seq [.raw " ", .text (.text s!"({f.doc})")]
    ]
  let body : Latex :=
    if fieldRows.isEmpty then .seq []
    else
      .seq [ .newline
           , .displayMath (.array none "rll" fieldRows)
           , .newline ]
  .envOpts "definition" s.docParam (.seq [
    .text s.doc,
    body
  ])

end StructDef
