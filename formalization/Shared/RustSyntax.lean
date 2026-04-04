/-- A Rust path like `std::cmp::Ordering::Less` or `Self`. -/
structure RustPath where
  segments : List String
  deriving Repr

/-- A Rust type expression. -/
inductive RustTy where
  /-- Named type: `Self`, `u32`, `Ordering`. -/
  | path (p : RustPath)
  /-- Reference: `&T` or `&mut T`. -/
  | ref (mutable : Bool) (inner : RustTy)
  /-- Generic type: `Option<T>`. -/
  | generic (base : RustPath) (args : List RustTy)
  /-- Unit type `()`. -/
  | unit
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
    /-- Let binding: `let pat: ty = val;`. -/
    | «let» (pat : RustPat) (ty : Option RustTy)
        (val : RustExpr)
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
  fields : List String
  deriving Repr

/-- An outer attribute. -/
inductive RustAttr where
  /-- `#[derive(Debug, Clone, ...)]`. -/
  | derive (traits : List String)
  /-- Arbitrary attribute text. -/
  | other (text : String)
  deriving Repr

/-- A top-level Rust item. -/
inductive RustItem where
  /-- An enum definition. -/
  | enum (doc : String) (attrs : List RustAttr)
      (vis : RustVis) (name : String)
      (variants : List RustVariant)
  /-- A tuple struct: `pub struct Foo(pub T1, pub T2);`. -/
  | tupleStruct (doc : String) (attrs : List RustAttr)
      (vis : RustVis) (name : String)
      (fields : List (RustVis × String))
  /-- A named-field struct. -/
  | struct_ (doc : String) (attrs : List RustAttr)
      (vis : RustVis) (name : String)
      (fields : List (RustVis × String × String))
  /-- An impl block (optionally for a trait). -/
  | impl_ (trait_ : Option RustPath) (ty : RustPath)
      (methods : List RustFn)
  /-- A standalone function. -/
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

/-- Construct a single-segment path. -/
def simple (s : String) : RustPath := ⟨[s]⟩

/-- The `Self` path. -/
def self_ : RustPath := simple "Self"

end RustPath

namespace RustTy

/-- The `Self` type. -/
def self_ : RustTy := .path RustPath.self_

/-- A named type. -/
def named (s : String) : RustTy := .path (RustPath.simple s)

/-- `Option<T>`. -/
def option (t : RustTy) : RustTy :=
  .generic ⟨["Option"]⟩ [t]

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

end RustExpr

namespace RustPat

/-- `Self::Variant` pattern. -/
def selfVariant (v : String) : RustPat :=
  .path ⟨["Self", v]⟩

end RustPat
