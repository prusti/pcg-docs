/-- A single variant in an exportable enum definition. -/
structure VariantDef where
  /-- The variant name (e.g. `"exclusive"`). -/
  name : String
  /-- Documentation for this variant. -/
  doc : String
  /-- Short LaTeX symbol (e.g. `"E"`). -/
  latex : String
  deriving Repr

/-- An exportable enum definition with metadata for cross-language
    code generation. -/
structure EnumDef where
  /-- The enum name (e.g. `"Capability"`). -/
  name : String
  /-- Top-level documentation. -/
  doc : String
  /-- The variants of the enum. -/
  variants : List VariantDef
  deriving Repr

namespace EnumDef

/-- Capitalise the first character of a string. -/
private def capitalise (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Wrap a documentation string as a Rust doc comment. -/
private def rustDocLine (s : String) : String :=
  s!"/// {s}"

/-- Generate a Rust `enum` definition. -/
def toRust (d : EnumDef) : String :=
  let header := s!"{rustDocLine d.doc}\n\
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]\n\
    pub enum {d.name} \{"
  let variantLines := d.variants.map fun v =>
    s!"    {rustDocLine v.doc}\n    {capitalise v.name},"
  let body := String.intercalate "\n" variantLines
  s!"{header}\n{body}\n}"

/-- Generate LaTeX `\newcommand` definitions. -/
def toLaTeX (d : EnumDef) : String :=
  let pfx := d.name.toLower
  let header := s!"% {d.name}: {d.doc}"
  let lines := d.variants.map fun v =>
    let cmdName := pfx ++ capitalise v.name
    let cmd := s!"\\newcommand\{\\{cmdName}}\{\\texttt\{{v.latex}}}"
    s!"% {v.doc}\n{cmd}"
  s!"{header}\n{String.intercalate "\n" lines}"

end EnumDef
