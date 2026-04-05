
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

namespace FType

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
  let s := s.trimAscii.toString
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
