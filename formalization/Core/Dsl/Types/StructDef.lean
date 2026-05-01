import Core.Export.Latex
import Core.Dsl.DslType
import Core.Dsl.Types.EnumDef

/-- A field of an exportable struct definition. -/
structure FieldDef where
  /-- The field name (e.g. `"id"`). -/
  name : String
  /-- The field type. -/
  ty : DSLType
  /-- Documentation for this field. -/
  doc : Doc
  /-- Symbol for this field's type (e.g. `τ` for `Ty`),
      looked up from the type's enum/struct definition.
      Used in constructor equations. -/
  symbolDoc : Option MathDoc := none
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
  /-- Top-level documentation. -/
  doc : Doc
  /-- Optional constructor name (e.g. `"LocalIdx"`).
      When set, renders as `sym ∈ set ::= Ctor(params)`.
      When `none`, renders with angle brackets. -/
  ctorName : Option String := none
  /-- Optional note (e.g. a URL) rendered as a footnote. -/
  note : Option String := none
  /-- Optional link URL. When set, the definition title
      becomes a hyperlink to this URL. -/
  link : Option String := none
  /-- Implicit type parameters (e.g. `["B", "I"]` for
      `LifetimeProjection {B I}`). These render as implicit
      type parameters in Lean and as generics in Rust. -/
  typeParams : List String := []
  /-- When `true`, the LaTeX presentation attaches the
      type parameters as a subscript to `symbolDoc` wherever
      the symbol is rendered in the formal definition
      (e.g. `rg_D` instead of `rg` for `RequiredGuide {D}`).
      Defaults to `false` so existing definitions are
      unaffected; opt in by passing `subscript` in the DSL. -/
  subscriptTypeParams : Bool := false
  /-- Optional display template for the right-hand side of
      the formal `sym ∈ Set ::= …` definition. When set, the
      template's literal fragments and field references are
      rendered in place of the default constructor or
      angle-bracket form. Field references resolve against the
      corresponding field's `symbolDoc` (the override if
      present, otherwise the type's `symbolDoc`).

      Constructor expressions (`Name⟨a, b, …⟩`) inside `defFn`
      bodies also render through this template — each `#field`
      reference is replaced by the rendered argument at the
      matching positional slot, so a `PlaceTriple⟨p, R, None⟩`
      constructor renders as `{R} p {None}` in the algorithm
      pretty-print rather than the Lean-source `PlaceTriple(p, R,
      None)`. -/
  display : Option (List DisplayPart) := none
  /-- The fields of the struct. -/
  fields : List FieldDef
  deriving Repr

namespace StructDef

/-- Render the struct's symbol for the formal definition,
    adding a `_{T₁ T₂ …}` subscript listing the type
    parameters when `subscriptTypeParams` is set. -/
def formalSymbolLatexMath (s : StructDef) : LatexMath :=
  let base := s.symbolDoc.toLatexMath
  if s.subscriptTypeParams && !s.typeParams.isEmpty then
    let subscript : LatexMath :=
      LatexMath.intercalate (.raw "~")
        (s.typeParams.map LatexMath.var)
    .sub base subscript
  else base

/-- Render the struct as a LaTeX `definition` environment. -/
def formalDefLatex (s : StructDef)
    (knownTypes : String → Bool := fun _ => false) : Latex :=
  let sym := s.formalSymbolLatexMath
  let sp := MathSym.space.toLatex
  let fieldSym (f : FieldDef) : LatexMath :=
    match f.symbolDoc with
    | some md => md.toLatexMath
    | none => .escaped f.name
  let fieldNames : LatexMath :=
    .seq (s.fields.map fun f =>
      .seq [sp, fieldSym f])
  let rhs : LatexMath := match s.display with
    | some parts =>
      .seq (parts.map DisplayPart.toLatexMath)
    | none => match s.ctorName with
      | some name =>
        .seq [.texttt name, fieldNames]
      | none =>
        let names := LatexMath.intercalate (.raw ",~")
          (s.fields.map fieldSym)
        .delimited "\\langle " "\\rangle" names
  let defLine : Latex :=
    if s.fields.isEmpty then .seq []
    else
      let typeParamsLM : LatexMath :=
        .seq (s.typeParams.flatMap fun p =>
          [.raw "~", .var p])
      let setDisplay : LatexMath :=
        .seq [s.setDoc.toLatexMath, typeParamsLM]
      .seq [
        .newline,
        .displayMath (.seq [
          sym, .raw " ", .cmd "in", .raw " ",
          setDisplay, .raw " ::= ", rhs]),
        .newline]
  let whereBlock : Latex :=
    if s.fields.isEmpty then .seq []
    else
      let fieldRows := s.fields.map fun f =>
        [ fieldSym f
        , .seq [.raw ": ",
                f.ty.toLatexMath knownTypes]
        , -- Wrap the description in a `\parbox` so long field
          -- descriptions wrap onto multiple lines instead of
          -- overflowing the array row. The width is
          -- `\linewidth - 9cm` so the box adapts to the
          -- remaining horizontal space after the first two
          -- columns and leaves enough room for wider type
          -- expressions (e.g. `Map K V` with hyperlinks).
          .seq [.raw "~", .text (Latex.parbox
            "\\dimexpr\\linewidth-9cm\\relax"
            (.seq [.raw "(", f.doc.toLatex, .raw ")"]))]
        ]
      .seq [.raw "where", .newline,
            .displayMath (.array none "rll" fieldRows),
            .newline]
  let noteFootnote : Latex := match s.note with
    | some url =>
      let escaped := url.replace "#" "\\#"
      .cmd "footnote" [.cmd "url" [.raw escaped]]
    | none => .seq []
  let title : Latex := match s.link with
    | some url => Latex.externalLink url (.text s.docParam)
    | none => .text s.docParam
  -- Invisible hypertargets so cross-references to this type
  -- (e.g. from function signatures, or via the `doc!` macro's
  -- `#X` shorthand which resolves to `fn:X`) can link here via
  -- `\hyperlink{type:<name>}{...}` or `\hyperlink{fn:<name>}{...}`.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{s.name}}\{}\\hypertarget\{fn:{s.name}}\{}"
  -- Render the prose description as a paragraph BEFORE the
  -- `definition` environment, so the formal `\begin{definition}
  -- ... \end{definition}` block contains only the formal
  -- syntax (sym ∈ Set ::= ...) and the where-block.
  .seq [
    s.doc.toLatex, noteFootnote, .newline,
    .envOpts "definition" title (.seq [
      typeTarget,
      defLine,
      whereBlock
    ])
  ]

end StructDef
