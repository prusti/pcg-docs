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

/-- A Rust module containing items. -/
structure RustModule where
  /-- Module name (snake_case). -/
  name : String
  /-- Top-level doc comment for the module. -/
  doc : String
  /-- Items in this module. -/
  items : List RustItem
  deriving Repr

/-- A Rust crate with Cargo metadata and modules. -/
structure RustCrate where
  /-- Crate name (kebab-case). -/
  name : String
  /-- Crate version. -/
  version : String
  /-- Crate description. -/
  description : String
  /-- Rust edition (e.g. `"2021"`). -/
  edition : String
  /-- The modules in the crate. -/
  modules : List RustModule
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

namespace RustModule

/-- Render a module to a complete Rust source file. -/
def render (m : RustModule) : String :=
  let header := s!"//! {m.doc}\n"
  let body := m.items.map (·.render)
  s!"{header}\n{String.intercalate "\n\n" body}\n"

/-- Render the `mod` declaration for `lib.rs`. -/
def modDecl (m : RustModule) : String :=
  s!"pub mod {m.name};"

end RustModule

namespace RustCrate

/-- Render the `Cargo.toml` for this crate. -/
def cargoToml (c : RustCrate) : String :=
  s!"[package]\n\
     name = \"{c.name}\"\n\
     version = \"{c.version}\"\n\
     edition = \"{c.edition}\"\n\
     description = \"{c.description}\"\n"

/-- Render `lib.rs` with module declarations. -/
def libRs (c : RustCrate) : String :=
  let mods := c.modules.map (·.modDecl)
  String.intercalate "\n" mods ++ "\n"

/-- All files in the crate as `(relative_path, contents)` pairs. -/
def files (c : RustCrate) : List (String × String) :=
  let cargoFile := ("Cargo.toml", c.cargoToml)
  let libFile := ("src/lib.rs", c.libRs)
  let modFiles := c.modules.map fun m =>
    (s!"src/{m.name}.rs", m.render)
  cargoFile :: libFile :: modFiles

end RustCrate

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
