import Core.Doc
import Core.Dsl.DslType

/-- A field of an exportable struct definition. -/
structure FieldDef where
  /-- The field name (e.g. `"id"`). -/
  name : String
  /-- The field type. -/
  ty : FType
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
