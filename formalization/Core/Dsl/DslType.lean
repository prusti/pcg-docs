import Core.Doc
import Core.Export.Latex

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
  /-- `Map K V` (rendered as `HashMap` in Rust). -/
  | map (key : DSLType) (val : DSLType)
  /-- `A × B × ...`. -/
  | tuple (parts : List DSLType)
  deriving Repr

instance : Inhabited DSLType := ⟨.prim .unit⟩

partial def DSLType.beq : DSLType → DSLType → Bool
  | .prim a, .prim b => a == b
  | .named a, .named b => a == b
  | .option a, .option b => DSLType.beq a b
  | .list a, .list b => DSLType.beq a b
  | .set a, .set b => DSLType.beq a b
  | .map ak av, .map bk bv =>
    DSLType.beq ak bk && DSLType.beq av bv
  | .tuple as, .tuple bs =>
    as.length == bs.length &&
      (as.zip bs).all fun (x, y) => DSLType.beq x y
  | _, _ => false

instance : BEq DSLType := ⟨DSLType.beq⟩

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
partial def toDoc : DSLType → OutputMode → Doc
  | .prim p, mode => p.toDoc mode
  | .named n, _ => .plain n.name
  | .option t, mode =>
    .seq [.plain "Option ", parenIfCompound t mode]
  | .list t, mode =>
    .seq [.plain "List ", parenIfCompound t mode]
  | .set t, mode =>
    .seq [.plain "Set ", parenIfCompound t mode]
  | .map k v, mode =>
    .seq [.plain "Map ",
          parenIfCompound k mode, .plain " ",
          parenIfCompound v mode]
  | .tuple parts, mode =>
    Doc.intercalate (.plain " × ")
      (parts.map fun t => t.toDoc mode)
where
  isCompound : DSLType → Bool
    | .prim _ => false
    | .named n => n.name.any fun c => c == ' ' || c == '×'
    | .option _ | .list _ | .set _ | .map _ _ | .tuple _ => true
  parenIfCompound (t : DSLType) (mode : OutputMode) : Doc :=
    if isCompound t then
      .seq [.plain "(", t.toDoc mode, .plain ")"]
    else t.toDoc mode

/-- Render a type to a text-mode `Latex` AST, inserting a
    `\hyperlink{type:<name>}{...}` for any named type whose
    name satisfies `knownTypes`. Non-linked types fall back
    to the `Doc`-based rendering. -/
partial def toLatex
    (knownTypes : String → Bool) : DSLType → Latex
  | .prim p => (p.toDoc .normal).toLatex
  | .named n =>
    if knownTypes n.name then
      -- `\protect` so the fragile `\hyperlink` survives
      -- moving arguments like `\caption{...}`.
      .raw s!"\\protect\\hyperlink\{type:{n.name}}\
             \{\\protect\\dashuline\{{n.name}}}"
    else .text n.name
  | .option t =>
    .seq [.raw "Option ", parenIfCompound knownTypes t]
  | .list t =>
    .seq [.raw "List ", parenIfCompound knownTypes t]
  | .set t =>
    .seq [.raw "Set ", parenIfCompound knownTypes t]
  | .map k v =>
    .seq [.raw "Map ",
          parenIfCompound knownTypes k, .raw " ",
          parenIfCompound knownTypes v]
  | .tuple parts =>
    .seq ((parts.map (toLatex knownTypes)).intersperse
      (.raw " × "))
where
  isCompound : DSLType → Bool
    | .prim _ => false
    | .named n => n.name.any fun c => c == ' ' || c == '×'
    | .option _ | .list _ | .set _ | .map _ _ | .tuple _ => true
  parenIfCompound (kt : String → Bool) (t : DSLType) : Latex :=
    if isCompound t then
      .seq [.raw "(", toLatex kt t, .raw ")"]
    else toLatex kt t

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

/-- Split a type string on top-level `×` separators
    (ignoring those nested inside parentheses). -/
private def splitTopLevelTimes (s : String) : List String :=
  let rec loop (cs : List Char) (depth : Nat)
      (cur : String) (acc : List String) : List String :=
    match cs with
    | [] => acc.reverse ++ [cur.trimAscii.toString]
    | c :: rest =>
      if c == '(' then
        loop rest (depth + 1) (cur.push c) acc
      else if c == ')' then
        loop rest (depth - 1) (cur.push c) acc
      else if depth == 0 && c == '×' then
        loop rest depth "" (cur.trimAscii.toString :: acc)
      else
        loop rest depth (cur.push c) acc
  loop s.toList 0 "" []

/-- Split a string into two top-level type arguments,
    respecting parentheses. E.g. `"Foo (Bar Baz)"` →
    `("Foo", "Bar Baz")`. -/
private def splitTwoArgs (s : String) : Option (String × String) :=
  let rec loop (cs : List Char) (depth : Nat)
      (cur : String) : Option (String × String) :=
    match cs with
    | [] => none
    | c :: rest =>
      if c == '(' then
        loop rest (depth + 1) (cur.push c)
      else if c == ')' then
        loop rest (depth - 1) (cur.push c)
      else if depth == 0 && c == ' ' &&
          !cur.trimAscii.isEmpty then
        let first := cur.trimAscii.toString
        let second := (String.ofList rest).trimAscii.toString
        if second.isEmpty then none
        else some (first, second)
      else
        loop rest depth (cur.push c)
  loop s.toList 0 ""

/-- Parse a Lean type string into a `DSLType`.
    Handles parenthesized types like
    `Option (Option Nat)`. -/
partial def parse (s : String) : DSLType :=
  let s := stripParens s
  let parts := splitTopLevelTimes s
  if parts.length > 1 then
    .tuple (parts.map parse)
  else
    match parsePrim s with
    | some p => .prim p
    | none =>
      if s.startsWith "Option " then
        .option (parse (s.drop 7).toString)
      else if s.startsWith "List " then
        .list (parse (s.drop 5).toString)
      else if s.startsWith "Set " then
        .set (parse (s.drop 4).toString)
      else if s.startsWith "Map " then
        let rest := (s.drop 4).toString
        match splitTwoArgs rest with
        | some (k, v) => .map (parse k) (parse v)
        | none => .named ⟨s⟩
      else .named ⟨s⟩

end DSLType
