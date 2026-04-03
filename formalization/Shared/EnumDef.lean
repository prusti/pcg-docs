import Shared.Doc

/-- A single variant in an exportable enum definition. -/
structure VariantDef where
  /-- The variant name (e.g. `"exclusive"`). -/
  name : String
  /-- Documentation for this variant. -/
  doc : String
  /-- Formatted symbol for document exports
      (e.g. `bold (text "E")`). -/
  symbolDoc : Doc
  /-- Human-readable display name for document exports
      (e.g. `seq [bold (text "E"), text "xclusive"]`). -/
  displayName : Doc
  deriving Repr

/-- An exportable enum definition with metadata for cross-language
    code generation and presentation. -/
structure EnumDef where
  /-- The enum name (e.g. `"Capability"`). -/
  name : String
  /-- Formatted type symbol for document exports. -/
  symbolDoc : Doc
  /-- Top-level documentation. -/
  doc : String
  /-- The variants of the enum. -/
  variants : List VariantDef
  deriving Repr

namespace EnumDef

/-- Short formal definition: `c ::= E | W | R | e` -/
def shortDef (d : EnumDef) : Doc :=
  let lhs := d.symbolDoc
  let rhs := Doc.intercalate (.text " | ")
    (d.variants.map fun v => v.symbolDoc)
  .seq [lhs, .text " ::= ", rhs]

/-- Long formal definition with descriptions:
    ```
    A capability c is one of:
    - **E**xclusive: Can be read, written, or mutably borrowed.
    - ...
    ``` -/
def longDef (d : EnumDef) : Doc :=
  let header := Doc.seq
    [.text d.doc, .text " ", d.symbolDoc,
     .text " is one of:"]
  let items := d.variants.map fun v =>
    Doc.seq [v.displayName, .text s!": {v.doc}"]
  .seq [header, .line, .itemize items]

end EnumDef
