import Shared.Doc

/-- A single variant in an exportable enum definition. -/
structure VariantDef where
  /-- The variant name (e.g. `"exclusive"`). -/
  name : String
  /-- Documentation for this variant. -/
  doc : String
  /-- Short symbol used in formal notation (e.g. `"E"`). -/
  symbol : String
  deriving Repr

/-- An exportable enum definition with metadata for cross-language
    code generation and presentation. -/
structure EnumDef where
  /-- The enum name (e.g. `"Capability"`). -/
  name : String
  /-- Symbol for the type in formal notation (e.g. `"c"`). -/
  symbol : String
  /-- Top-level documentation. -/
  doc : String
  /-- The variants of the enum. -/
  variants : List VariantDef
  deriving Repr

namespace EnumDef

/-- Short formal definition: `c ::= E | W | R | e` -/
def shortDef (d : EnumDef) : Doc :=
  let lhs := Doc.italic (.text d.symbol)
  let rhs := Doc.intercalate (.text " | ")
    (d.variants.map fun v => .bold (.text v.symbol))
  .seq [lhs, .text " ::= ", rhs]

/-- Long formal definition with descriptions:
    ```
    A capability c is one of:
    - E (exclusive): Can be read, written, or mutably borrowed.
    - ...
    ``` -/
def longDef (d : EnumDef) : Doc :=
  let header := Doc.seq
    [.text d.doc, .text " ", .italic (.text d.symbol),
     .text " is one of:"]
  let items := d.variants.map fun v =>
    Doc.seq
      [.bold (.text v.symbol),
       .text s!" ({v.name}): {v.doc}"]
  .seq [header, .line, .itemize items]

end EnumDef
