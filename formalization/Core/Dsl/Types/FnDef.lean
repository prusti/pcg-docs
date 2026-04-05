import Core.Doc
import Core.Dsl.Types.StructDef
import Core.Dsl.DslType

/-- A pattern in a function body. -/
inductive BodyPat where
  | wild
  | var (name : String)
  | ctor (name : String) (args : List BodyPat)
  /-- Empty list pattern: `[]`. -/
  | nil
  /-- List cons pattern: `h :: t`. -/
  | cons (head : BodyPat) (tail : BodyPat)
  deriving Repr

/-- An expression in the function body DSL. -/
inductive BodyExpr where
  | var (name : String)
  | true_
  | false_
  | emptyList
  | none_
  | some_ (e : BodyExpr)
  /-- Struct constructor. `name` is the struct name
      (empty for anonymous tuples). -/
  | mkStruct (name : String) (args : List BodyExpr)
  | cons (head : BodyExpr) (tail : BodyExpr)
  | append (lhs : BodyExpr) (rhs : BodyExpr)
  | dot (recv : BodyExpr) (method : String)
  | flatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : BodyExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : BodyExpr) (idx : BodyExpr)
  /-- Infallible list indexing: `list[idx]`. -/
  | indexBang (list : BodyExpr) (idx : BodyExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : String) (args : List BodyExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : String) (init : BodyExpr)
      (list : BodyExpr)
  /-- Less-than comparison: `lhs < rhs`. -/
  | lt (lhs : BodyExpr) (rhs : BodyExpr)
  deriving Repr

/-- A statement in a do-block. -/
inductive BodyStmt where
  /-- `let name := val`. -/
  | let_ (name : String) (val : BodyExpr)
  /-- `let name ← val` (monadic bind). -/
  | letBind (name : String) (val : BodyExpr)
  deriving Repr

/-- A match arm: patterns → expression. -/
structure BodyArm where
  pat : List BodyPat
  rhs : BodyExpr
  deriving Repr

/-- A function body: either pattern-matching arms or an
    imperative do-block. -/
inductive FnBody where
  /-- Pattern-matching function. -/
  | matchArms (arms : List BodyArm)
  /-- Imperative do-block with let bindings. -/
  | doBlock (stmts : List BodyStmt) (ret : BodyExpr)
  deriving Repr

/-- An exportable function definition. -/
structure FnDef where
  name : String
  symbolDoc : Doc
  doc : String
  params : List FieldDef
  returnType : DSLType
  /-- Names of properties that must hold before calling
      this function. -/
  preconditions : List String := []
  body : FnBody
  deriving Repr

-- ══════════════════════════════════════════════
-- Quote instances
-- ══════════════════════════════════════════════

open Lean in
partial def quotePat : BodyPat → TSyntax `term
  | .wild => Syntax.mkApp (mkIdent ``BodyPat.wild) #[]
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyPat.var) #[quote n]
  | .ctor n args =>
    let qArgs := args.map quotePat
    Syntax.mkApp (mkIdent ``BodyPat.ctor)
      #[quote n, quote qArgs]
  | .nil =>
    Syntax.mkApp (mkIdent ``BodyPat.nil) #[]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyPat.cons)
      #[quotePat h, quotePat t]

open Lean in
instance : Quote BodyPat where quote := quotePat

open Lean in
partial def quoteExpr : BodyExpr → TSyntax `term
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyExpr.var) #[quote n]
  | .true_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.true_) #[]
  | .false_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.false_) #[]
  | .emptyList =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptyList) #[]
  | .none_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.none_) #[]
  | .some_ e =>
    Syntax.mkApp (mkIdent ``BodyExpr.some_)
      #[quoteExpr e]
  | .mkStruct name args =>
    Syntax.mkApp (mkIdent ``BodyExpr.mkStruct)
      #[quote name, quote (args.map quoteExpr)]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyExpr.cons)
      #[quoteExpr h, quoteExpr t]
  | .append l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.append)
      #[quoteExpr l, quoteExpr r]
  | .dot recv method =>
    Syntax.mkApp (mkIdent ``BodyExpr.dot)
      #[quoteExpr recv, quote method]
  | .flatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.flatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .field recv name =>
    Syntax.mkApp (mkIdent ``BodyExpr.field)
      #[quoteExpr recv, quote name]
  | .index list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.index)
      #[quoteExpr list, quoteExpr idx]
  | .indexBang list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.indexBang)
      #[quoteExpr list, quoteExpr idx]
  | .call fn args =>
    Syntax.mkApp (mkIdent ``BodyExpr.call)
      #[quote fn, quote (args.map quoteExpr)]
  | .foldlM fn init list =>
    Syntax.mkApp (mkIdent ``BodyExpr.foldlM)
      #[quote fn, quoteExpr init, quoteExpr list]
  | .lt l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.lt)
      #[quoteExpr l, quoteExpr r]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

namespace BodyPat

partial def toRust (enumName : String)
    : BodyPat → String
  | .wild => "_"
  | .var n => n.replace "τ₀" "ty0"
    |>.replace "τ" "ty" |>.replace "π" "pi"
  | .ctor "⟨⟩" args =>
    -- Struct destructure: render children without
    -- enum qualification.
    s!"({", ".intercalate
      (args.map (toRust ""))})"
  | .ctor n args =>
    let capName := String.ofList
      (n.toList.head!.toUpper :: n.toList.tail!)
    let argStr := ", ".intercalate
      (args.map (toRust enumName))
    if enumName.isEmpty then
      -- Inside a struct destructure: bare variant
      if args.isEmpty then capName
      else s!"{capName}({argStr})"
    else if args.isEmpty then
      s!"{enumName}::{capName}"
    else
      s!"{enumName}::{capName}({argStr})"
  | .nil => "[]"
  | .cons h tail =>
    let elemName := if enumName.startsWith "List "
      then enumName.drop 5 |>.toString
      else enumName
    let hStr := h.toRust elemName
    let tailStr := match tail with
      | .var rest =>
        let rv := rest.replace "τ" "ty"
          |>.replace "π" "pi"
        s!", {rv} @ .."
      | .wild => ", .."
      | _ => s!", {tail.toRust elemName} @ .."
    s!"[{hStr}{tailStr}]"

end BodyPat
