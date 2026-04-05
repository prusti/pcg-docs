
/-- A primitive type. -/
inductive DSLPrimTy where
  | nat
  | string
  | bool
  | unit
  | u8
  | u16
  | u32
  | u64
  | usize
  deriving Repr, DecidableEq

/-- A named type from `defEnum` or `defStruct`. -/
structure DSLNamedTy where
  /-- The type name. -/
  name : String
  deriving Repr, DecidableEq, Inhabited

/-- A structured type used in function signatures and
    the body DSL. Allows the Rust renderer to make correct
    decisions about cloning, boxing, references, etc. -/
inductive DSLType where
  /-- A primitive type. -/
  | prim (p : DSLPrimTy)
  /-- A named type from `defEnum` or `defStruct`. -/
  | named (n : DSLNamedTy)
  /-- `Option T`. -/
  | option (inner : DSLType)
  /-- `List T`. -/
  | list (inner : DSLType)
  deriving Repr, DecidableEq, Inhabited

namespace DSLType

/-- Whether this type needs `Box` wrapping in Rust
    when it's self-referential (appears inside its own
    enum definition). -/
def isRecursiveIn (typeName : String) : DSLType → Bool
  | .named n => n.name == typeName
  | .option t => t.isRecursiveIn typeName
  | .list _ => false  -- Vec handles indirection
  | .prim _ => false

/-- Strip `Option` wrapper if present. -/
def stripOption : DSLType → DSLType
  | .option t => t
  | t => t

/-- Strip balanced outer parentheses, e.g.
    `"(Option Nat)"` → `"Option Nat"`. -/
private def stripParens (s : String) : String :=
  let s := s.trimAscii.toString
  if s.startsWith "(" && s.endsWith ")" then
    (s.drop 1 |>.dropEnd 1).trimAscii.toString
  else s

/-- Try to parse a primitive type name. -/
private def parsePrim : String → Option DSLPrimTy
  | "Nat" => some .nat
  | "String" => some .string
  | "Bool" => some .bool
  | "Unit" | "()" => some .unit
  | "UInt8" => some .u8
  | "UInt16" => some .u16
  | "UInt32" => some .u32
  | "UInt64" => some .u64
  | "USize" => some .usize
  | _ => none

/-- Parse a Lean type string into a `DSLType`.
    Handles parenthesized types like
    `Option (Option Nat)`. -/
partial def parse (s : String) : DSLType :=
  let s := stripParens s
  match parsePrim s with
  | some p => .prim p
  | none =>
    if s.startsWith "Option " then
      .option (parse (s.drop 7).toString)
    else if s.startsWith "List " then
      .list (parse (s.drop 5).toString)
    else .named ⟨s⟩

end DSLType
