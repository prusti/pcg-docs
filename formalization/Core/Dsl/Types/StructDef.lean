import Core.Doc
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
  /-- Top-level documentation. -/
  doc : String
  /-- The fields of the struct. -/
  fields : List FieldDef
  deriving Repr

namespace StructDef

/-- Render the struct as a LaTeX `definition` environment. -/
def formalDefLatex (s : StructDef) : String :=
  let lb := "{"
  let rb := "}"
  let fieldRows := s.fields.map fun f =>
    s!"  {Doc.escapeLatexMath f.name} &: \
       {(f.ty.toDoc .math).toLatexMath} & \
       \\text{lb}({Doc.escapeLatex f.doc}){rb} \\\\"
  let body := if fieldRows.isEmpty then ""
    else
      s!"\n\\[ \\begin{lb}array{rb}{lb}rll{rb}\n\
         {"\n".intercalate fieldRows}\n\
         \\end{lb}array{rb} \\]\n"
  s!"\\begin{lb}definition{rb}[{s.name}]\n\
     {Doc.escapeLatex s.doc}\
     {body}\
     \\end{lb}definition{rb}"

end StructDef
