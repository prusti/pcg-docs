import Shared.EnumDef

/-- A Rust derive macro name. -/
structure RustDerive where
  name : String
  deriving Repr

/-- A Rust enum variant. -/
structure RustVariant where
  /-- Doc comment lines. -/
  doc : String
  /-- Variant name (PascalCase). -/
  name : String
  deriving Repr

/-- A top-level Rust item. -/
inductive RustItem where
  /-- An enum definition. -/
  | enum
    (doc : String)
    (derives : List RustDerive)
    (name : String)
    (variants : List RustVariant)
  deriving Repr

namespace RustItem

/-- Render a `RustItem` to Rust source code. -/
def render : RustItem → String
  | .enum doc derives name variants =>
    let deriveLine := if derives.isEmpty then ""
      else
        let names := derives.map (·.name)
        s!"#[derive({String.intercalate ", " names})]\n"
    let variantLines := variants.map fun v =>
      s!"    /// {v.doc}\n    {v.name},"
    s!"/// {doc}\n\
       {deriveLine}\
       pub enum {name} \{\n\
       {String.intercalate "\n" variantLines}\n\
       }"

end RustItem

namespace EnumDef

/-- Capitalise the first character of a string. -/
private def capitalise (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Standard derives for a simple Rust enum. -/
private def defaultDerives : List RustDerive :=
  [⟨"Debug"⟩, ⟨"Clone"⟩, ⟨"Copy"⟩,
   ⟨"PartialEq"⟩, ⟨"Eq"⟩, ⟨"Hash"⟩]

/-- Convert an `EnumDef` to a `RustItem.enum`. -/
def toRustItem (d : EnumDef) : RustItem :=
  .enum d.doc defaultDerives d.name
    (d.variants.map fun v =>
      { doc := v.doc, name := capitalise v.name })

/-- Generate Rust source code for this enum. -/
def toRust (d : EnumDef) : String :=
  d.toRustItem.render

end EnumDef
