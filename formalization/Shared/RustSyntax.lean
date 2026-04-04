/-- A Rust path like `std::cmp::Ordering::Less` or `Self`. -/
structure RustPath where
  segments : List String
  deriving Repr

/-- A Rust built-in (primitive) type. -/
inductive RustBuiltinTy where
  | unit    -- ()
  | bool    -- bool
  | usize   -- usize
  | u8 | u16 | u32 | u64 | u128
  | i8 | i16 | i32 | i64 | i128
  | f32 | f64
  | str     -- str (unsized)
  | string  -- String
  deriving Repr

/-- A Rust type expression. -/
inductive RustTy where
  /-- A built-in primitive type. -/
  | builtin (ty : RustBuiltinTy)
  /-- Reference: `&T` or `&mut T`. -/
  | ref (mutable : Bool) (inner : RustTy)
  /-- An ADT (struct/enum) type, possibly with type
      arguments: `Foo`, `Option<T>`, `Vec<T>`. -/
  | adt (constructor : RustPath) (args : List RustTy)
  /-- `impl Into<T>` argument type. -/
  | implInto (inner : RustTy)
  /-- Slice type: `[T]`. -/
  | slice (inner : RustTy)
  deriving Repr

/-- A unary operator. -/
inductive RustUnaryOp where
  | deref   -- *expr
  | neg     -- -expr
  | not     -- !expr
  deriving Repr

/-- A binary operator. -/
inductive RustBinOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr

/-- A Rust pattern. -/
inductive RustPat where
  /-- Variable binding: `x`. -/
  | ident (name : String)
  /-- Wildcard: `_`. -/
  | wild
  /-- Tuple pattern: `(a, b)`. -/
  | tuple (pats : List RustPat)
  /-- Path pattern: `Self::Variant`. -/
  | path (p : RustPath)
  /-- Reference pattern: `&x`. -/
  | ref (inner : RustPat)
  /-- Or pattern: `A | B | C`. -/
  | or (pats : List RustPat)
  deriving Repr

mutual
  /-- A Rust expression. -/
  inductive RustExpr where
    /-- Path expression: `std::cmp::Ordering::Less`. -/
    | path (p : RustPath)
    /-- String literal. -/
    | litStr (s : String)
    /-- Boolean literal. -/
    | litBool (b : Bool)
    /-- Function call: `f(a, b)`. -/
    | call (func : RustExpr) (args : List RustExpr)
    /-- Method call: `x.method(a, b)`. -/
    | methodCall (recv : RustExpr)
        (method : String) (args : List RustExpr)
    /-- Field access: `x.field`. -/
    | field (recv : RustExpr) (name : String)
    /-- Unary operation: `*expr`, `-expr`, `!expr`. -/
    | unaryOp (op : RustUnaryOp) (e : RustExpr)
    /-- Binary operation: `a == b`. -/
    | binOp (op : RustBinOp) (lhs rhs : RustExpr)
    /-- Tuple expression: `(a, b)`. -/
    | tuple (elems : List RustExpr)
    /-- Block expression: `{ stmts; expr? }`. -/
    | block (stmts : List RustStmt)
        (expr : Option RustExpr)
    /-- If expression: `if cond { ... } else { ... }`. -/
    | «if» (cond : RustExpr) (then_ : RustExpr)
        (else_ : Option RustExpr)
    /-- Match expression. -/
    | «match» (scrutinee : RustExpr)
        (arms : List RustMatchArm)
    /-- Return statement: `return expr`. -/
    | «return» (val : Option RustExpr)
    /-- `&expr` (borrow). -/
    | ref_ (mutable : Bool) (e : RustExpr)
    /-- `expr?` (try operator). -/
    | try_ (e : RustExpr)
    /-- Closure: `|params| body`. -/
    | closure (params : List String) (body : RustExpr)
    /-- Struct literal: `Path { field: expr, ... }`. -/
    | structInit (path : RustPath)
        (fields : List (String × RustExpr))
    /-- Raw string (for macros like `vec![]`,
        `todo!()`). -/
    | raw (s : String)

  /-- A match arm: `pat => expr`. -/
  inductive RustMatchArm where
    | mk (pat : RustPat) (body : RustExpr)

  /-- A Rust statement. -/
  inductive RustStmt where
    /-- Expression statement: `expr;`. -/
    | expr (e : RustExpr)
    /-- Let binding: `let [mut] pat: ty = val;`. -/
    | «let» (pat : RustPat) (ty : Option RustTy)
        (val : RustExpr) (mutable : Bool := false)
end

/-- A function parameter. -/
inductive RustParam where
  /-- `&self` parameter. -/
  | selfRef
  /-- `&mut self` parameter. -/
  | selfMut
  /-- Named parameter: `name: ty`. -/
  | named (name : RustPat) (ty : RustTy)
  deriving Repr

/-- Visibility of a Rust item. -/
inductive RustVis where
  | priv
  | pub
  deriving Repr

/-- A function definition. -/
structure RustFn where
  vis : RustVis
  name : String
  params : List RustParam
  retTy : Option RustTy
  body : RustExpr

/-- An enum variant, optionally with tuple fields. -/
structure RustVariant where
  /-- Doc comment. -/
  doc : String
  /-- Variant name (PascalCase). -/
  name : String
  /-- Tuple field types (empty for unit variants). -/
  fields : List RustTy
  deriving Repr

/-- An outer attribute. -/
inductive RustAttr where
  /-- `#[derive(Debug, Clone, ...)]`. -/
  | derive (traits : List String)
  /-- Arbitrary attribute text. -/
  | other (text : String)
  deriving Repr

/-- A Rust enum definition. -/
structure RustEnum where
  doc : String
  attrs : List RustAttr
  vis : RustVis
  name : String
  variants : List RustVariant
  deriving Repr

/-- Struct fields: either positional (tuple struct) or
    named (regular struct). -/
inductive RustStructFields where
  /-- Positional fields: `(pub T1, pub T2)`. -/
  | unnamed (fields : List (RustVis × RustTy))
  /-- Named fields: `{ pub name: T }`. -/
  | named (fields : List (RustVis × String × RustTy))
  deriving Repr

/-- A Rust struct (tuple or named-field). -/
structure RustStruct where
  doc : String
  attrs : List RustAttr
  vis : RustVis
  name : String
  fields : RustStructFields
  deriving Repr

/-- A Rust impl block. -/
structure RustImpl where
  /-- The trait being implemented (`None` for inherent). -/
  trait_ : Option RustPath
  /-- The type being implemented. -/
  ty : RustPath
  /-- The methods in the impl block. -/
  methods : List RustFn

/-- A top-level Rust item. -/
inductive RustItem where
  | enum (e : RustEnum)
  | struct_ (s : RustStruct)
  | impl_ (i : RustImpl)
  | fn_ (f : RustFn)

/-- A Rust module containing items. -/
structure RustModule where
  /-- Module name (snake_case). -/
  name : String
  /-- Top-level doc comment for the module. -/
  doc : String
  /-- Items in this module. -/
  items : List RustItem

/-- A dependency of a Rust crate. -/
structure RustCrateDep where
  /-- Dependency crate name. -/
  name : String
  /-- Relative path to the dependency crate. -/
  path : String
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
  /-- Path dependencies. -/
  deps : List RustCrateDep := []
  /-- Crate-level attributes (e.g. `deny(clippy::all)`). -/
  crateAttrs : List String := []
  /-- Dependency crate names to re-export via `pub use`. -/
  reexports : List String := []

/-- A Cargo workspace containing multiple crates. -/
structure RustWorkspace where
  /-- Crate directory names (relative to workspace root). -/
  members : List String
  deriving Repr

instance : Inhabited RustExpr where
  default := .raw ""

namespace RustPath

/-- Render a path: `std::cmp::Ordering::Less`. -/
def render (p : RustPath) : String :=
  String.intercalate "::" p.segments

/-- Construct a single-segment path. -/
def simple (s : String) : RustPath := ⟨[s]⟩

/-- The `Self` path. -/
def self_ : RustPath := simple "Self"

end RustPath

namespace RustBuiltinTy

/-- Render a built-in type to its Rust name. -/
def render : RustBuiltinTy → String
  | .unit => "()"
  | .bool => "bool"
  | .usize => "usize"
  | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128"
  | .i8 => "i8" | .i16 => "i16"
  | .i32 => "i32" | .i64 => "i64" | .i128 => "i128"
  | .f32 => "f32" | .f64 => "f64"
  | .str => "str" | .string => "String"

end RustBuiltinTy

namespace RustTy

/-- Render a type expression. -/
def render : RustTy → String
  | .builtin b => b.render
  | .ref true inner => s!"&mut {inner.render}"
  | .ref false inner => s!"&{inner.render}"
  | .adt ctor args =>
    if args.isEmpty then ctor.render
    else
      let argStrs := args.map RustTy.render
      s!"{ctor.render}<{String.intercalate ", " argStrs}>"
  | .implInto inner => s!"impl Into<{inner.render}>"
  | .slice inner => s!"[{inner.render}]"

/-- The `Self` type. -/
def self_ : RustTy := .adt RustPath.self_ []

/-- A named type (no type arguments). -/
def named (s : String) : RustTy :=
  .adt (RustPath.simple s) []

/-- `Option<T>`. -/
def option (t : RustTy) : RustTy :=
  .adt ⟨["Option"]⟩ [t]

/-- `&T`. -/
def refTo (t : RustTy) : RustTy := .ref false t

end RustTy

namespace RustExpr

/-- Path expression from segments. -/
def pathOf (segments : List String) : RustExpr :=
  .path ⟨segments⟩

/-- `None`. -/
def none_ : RustExpr := pathOf ["None"]

/-- `Some(e)`. -/
def some_ (e : RustExpr) : RustExpr :=
  .call (pathOf ["Some"]) [e]

/-- `vec![]` (empty vector macro). -/
def emptyVec : RustExpr := .raw "vec![]"

/-- `expr.clone()`. -/
def clone (e : RustExpr) : RustExpr :=
  .methodCall e "clone" []

/-- `*expr`. -/
def deref (e : RustExpr) : RustExpr :=
  .unaryOp .deref e

/-- `&expr`. -/
def borrow (e : RustExpr) : RustExpr :=
  .ref_ false e

/-- `&mut expr`. -/
def borrowMut (e : RustExpr) : RustExpr :=
  .ref_ true e

/-- `todo!()`. -/
def todo : RustExpr := .raw "todo!()"

/-- A simple identifier expression. -/
def ident (s : String) : RustExpr :=
  .path (.simple s)

end RustExpr

namespace RustPat

/-- `Self::Variant` pattern. -/
def selfVariant (v : String) : RustPat :=
  .path ⟨["Self", v]⟩

end RustPat
