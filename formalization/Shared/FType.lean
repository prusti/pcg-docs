import Shared.Doc
import Shared.RustSyntax

/-- A primitive type. -/
inductive FPrim where
  | nat
  | string
  | bool
  | unit
  deriving Repr, DecidableEq

/-- A structured type used in function signatures and
    the body DSL. Allows the Rust renderer to make correct
    decisions about cloning, boxing, references, etc. -/
inductive FType where
  /-- A primitive type. -/
  | prim (p : FPrim)
  /-- A named type from `defEnum` or `defStruct`. -/
  | named (name : String)
  /-- `Option T`. -/
  | option (inner : FType)
  /-- `List T`. -/
  | list (inner : FType)
  deriving Repr, DecidableEq, Inhabited

namespace FPrim

/-- Render a primitive to Lean syntax. -/
def toLean : FPrim → String
  | .nat => "Nat"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "Unit"

/-- Render a primitive to a Rust type string. -/
def toRustStr : FPrim → String
  | .nat => "usize"
  | .string => "String"
  | .bool => "bool"
  | .unit => "()"

/-- Convert to a `RustBuiltinTy`. -/
def toRust : FPrim → RustBuiltinTy
  | .nat => .usize
  | .string => .string
  | .bool => .bool
  | .unit => .unit

/-- Render a primitive to LaTeX (text mode). -/
def toLatex : FPrim → String
  | .nat => "$\\mathbb{N}$"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "()"

/-- Render a primitive to LaTeX math mode. -/
def toLatexMath : FPrim → String
  | .nat => "\\mathbb{N}"
  | .string => "\\text{String}"
  | .bool => "\\text{Bool}"
  | .unit => "()"

end FPrim

namespace FType

/-- Render a type to Lean syntax. -/
def toLean : FType → String
  | .prim p => p.toLean
  | .named n => n
  | .option t => s!"Option {t.toLean}"
  | .list t => s!"List {t.toLean}"

/-- Render a type to a Rust type string. -/
def toRustStr : FType → String
  | .prim p => p.toRustStr
  | .named n => n
  | .option t => s!"Option<{t.toRustStr}>"
  | .list t => s!"Vec<{t.toRustStr}>"

/-- Convert to a typed `RustTy`. -/
def toRust : FType → RustTy
  | .prim p => .builtin p.toRust
  | .named n => .named n
  | .option t => .option t.toRust
  | .list t => .adt ⟨["Vec"]⟩ [t.toRust]

/-- Render a type to LaTeX (text mode). -/
def toLatex : FType → String
  | .prim p => p.toLatex
  | .named n => Doc.escapeLatex n
  | .option t => s!"Option {t.toLatex}"
  | .list t => s!"List {t.toLatex}"

/-- Render a type to LaTeX math mode. -/
def toLatexMath : FType → String
  | .prim p => p.toLatexMath
  | .named n => Doc.escapeLatexMath n
  | .option t =>
    s!"\\text{lb}Option{rb}~{t.toLatexMath}"
  | .list t =>
    s!"\\text{lb}List{rb}~{t.toLatexMath}"
  where lb := "{" ; rb := "}"

/-- Whether this type needs `Box` wrapping in Rust
    when it's self-referential (appears inside its own
    enum definition). -/
def isRecursiveIn (typeName : String) : FType → Bool
  | .named n => n == typeName
  | .option t => t.isRecursiveIn typeName
  | .list _ => false  -- Vec handles indirection
  | .prim _ => false

/-- Strip `Option` wrapper if present. -/
def stripOption : FType → FType
  | .option t => t
  | t => t

/-- Parse a Lean type string into an `FType`. -/
partial def parse (s : String) : FType :=
  let s := s.trim
  if s == "Nat" then .prim .nat
  else if s == "String" then .prim .string
  else if s == "Bool" then .prim .bool
  else if s == "Unit" || s == "()" then .prim .unit
  else if s.startsWith "Option " then
    .option (parse (s.drop 7).toString)
  else if s.startsWith "List " then
    .list (parse (s.drop 5).toString)
  else .named s

end FType
