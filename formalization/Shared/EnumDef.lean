import Shared.Doc

/-- An argument of an enum variant (e.g. `v : RegionVid`). -/
structure ArgDef where
  /-- The argument name (e.g. `"v"`). -/
  name : String
  /-- The argument type name (e.g. `"RegionVid"`). -/
  typeName : String
  deriving Repr

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
  /-- Arguments of this variant (empty for nullary variants). -/
  args : List ArgDef
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

namespace VariantDef

/-- Append rendered arguments to a base `Doc`.
    Returns `base` unchanged when `args` is empty;
    otherwise produces `base(arg₁, arg₂, …)`. -/
private def withArgs
    (base : Doc)
    (renderArg : ArgDef → Doc)
    (args : List ArgDef)
    : Doc :=
  if args.isEmpty then base
  else
    .seq [base, .text "(",
          Doc.intercalate (.text ", ")
            (args.map renderArg),
          .text ")"]

/-- Render the variant symbol with arguments for short definitions.
    Nullary: `E`. With args: `vid(v)`. -/
def symbolWithArgs (v : VariantDef) : Doc :=
  withArgs v.symbolDoc
    (fun a => .text a.name) v.args

/-- Render the variant display name with typed arguments for long
    definitions. Nullary: `Exclusive`. With args:
    `vid(v : RegionVid)`. -/
def displayWithArgs (v : VariantDef) : Doc :=
  withArgs v.displayName
    (fun a => .text s!"{a.name} : {a.typeName}") v.args

end VariantDef

namespace EnumDef

/-- Short formal definition: `c ::= E | W | R | e` -/
def shortDef (d : EnumDef) : Doc :=
  let lhs := d.symbolDoc
  let rhs := Doc.intercalate (.text " | ")
    (d.variants.map fun v => v.symbolWithArgs)
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
    Doc.seq [v.displayWithArgs, .text s!": {v.doc}"]
  .seq [header, .line, .itemize items]

/-- Render the enum as a LaTeX `definition` environment with
    an aligned `array`:
    ```
    \begin{definition}[Region]
    A region ...
    \[ r ::= \begin{array}[t]{rll}
         & \text{vid}(v) & \text{(A region variable ...)} \\
       \mid & \texttt{'static} & \text{(The ...)} \\
    \end{array} \]
    \end{definition}
    ``` -/
def formalDefLatex (d : EnumDef) : String :=
  let lb := "{"
  let rb := "}"
  let sym := d.symbolDoc.toLaTeX
  let rows := d.variants.zipIdx.map fun (v, i) =>
    let sep := if i == 0 then "  " else "\\mid"
    let variant := v.symbolWithArgs.toLaTeX
    let desc := Doc.escapeLatex v.doc
    s!"  {sep} & {variant} & \
       \\text{lb}({desc}){rb} \\\\"
  let arrayBody := "\n".intercalate rows
  s!"\\begin{lb}definition{rb}[{d.name}]\n\
     {Doc.escapeLatex d.doc}\n\
     \\[ {sym} ::= \\begin{lb}array{rb}[t]\
     {lb}rll{rb}\n\
     {arrayBody}\n\
     \\end{lb}array{rb} \\]\n\
     \\end{lb}definition{rb}"

end EnumDef
