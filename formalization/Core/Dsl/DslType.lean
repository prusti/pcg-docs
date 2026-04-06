import Core.Doc

/-- Output mode for rendering types. -/
inductive OutputMode where
  /-- Math mode (inside `\[ ... \]`). -/
  | math
  /-- Normal text mode. -/
  | normal
  deriving Repr, DecidableEq

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
  /-- `Set T` (rendered as `HashSet` in Rust). -/
  | set (inner : DSLType)
  deriving Repr, DecidableEq, Inhabited

namespace DSLPrimTy

/-- Render a primitive type to a `Doc`. -/
def toDoc : DSLPrimTy → OutputMode → Doc
  | .nat, .normal => .math (.bb (.raw "N"))
  | .nat, .math => .math (.bb (.raw "N"))
  | .string, _ => .plain "String"
  | .bool, _ => .plain "Bool"
  | .unit, _ => .plain "()"
  | .u8, .normal => .plain "u8"
  | .u8, .math => .code "u8"
  | .u16, .normal => .plain "u16"
  | .u16, .math => .code "u16"
  | .u32, .normal => .plain "u32"
  | .u32, .math => .code "u32"
  | .u64, .normal => .plain "u64"
  | .u64, .math => .code "u64"
  | .usize, .normal => .plain "usize"
  | .usize, .math => .code "usize"

end DSLPrimTy

namespace DSLType

/-- Render a type to a `Doc`. -/
def toDoc : DSLType → OutputMode → Doc
  | .prim p, mode => p.toDoc mode
  | .named n, _ => .plain n.name
  | .option t, mode =>
    .seq [.plain "Option ", t.toDoc mode]
  | .list t, mode =>
    .seq [.plain "List ", t.toDoc mode]
  | .set t, mode =>
    .seq [.plain "Set ", t.toDoc mode]

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
    else if s.startsWith "Set " then
      .set (parse (s.drop 4).toString)
    else .named ⟨s⟩

end DSLType
