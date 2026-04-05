import Core.FType
import Core.FnDef
import Core.StructDef

-- ══════════════════════════════════════════════
-- Lean rendering for FPrim / FType
-- ══════════════════════════════════════════════

namespace FPrim

/-- Render a primitive to Lean syntax. -/
def toLean : FPrim → String
  | .nat => "Nat"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "Unit"

end FPrim

namespace FType

/-- Render a type to Lean syntax. -/
def toLean : FType → String
  | .prim p => p.toLean
  | .named n => n
  | .option t => s!"Option {t.toLean}"
  | .list t => s!"List {t.toLean}"

end FType

-- ══════════════════════════════════════════════
-- Lean rendering for StructDef
-- ══════════════════════════════════════════════

namespace FieldDef

/-- Backward-compatible accessor. -/
def typeName (f : FieldDef) : String :=
  f.ty.toLean

end FieldDef

-- ══════════════════════════════════════════════
-- Lean rendering for BodyPat / BodyExpr / FnBody
-- ══════════════════════════════════════════════

namespace BodyPat

partial def toLean : BodyPat → String
  | .wild => "_"
  | .var n => n
  | .ctor "⟨⟩" args =>
    s!"⟨{", ".intercalate (args.map toLean)}⟩"
  | .ctor n args =>
    if args.isEmpty then s!".{n}"
    else s!".{n} {" ".intercalate (args.map toLean)}"
  | .nil => "[]"
  | .cons h t => s!"{h.toLean} :: {t.toLean}"

end BodyPat

namespace BodyExpr

mutual
/-- Render an expression as a Lean function argument,
    parenthesizing compound expressions. -/
partial def toLeanArg : BodyExpr → String
  | .var n => n
  | .true_ => "true"
  | .false_ => "false"
  | .none_ => "none"
  | .emptyList => "[]"
  | e => s!"({e.toLean})"

partial def toLean : BodyExpr → String
  | .var n => n
  | .true_ => "true"
  | .false_ => "false"
  | .emptyList => "[]"
  | .none_ => "none"
  | .some_ e => s!"some {e.toLean}"
  | .mkStruct _ args =>
    s!"⟨{", ".intercalate (args.map toLean)}⟩"
  | .cons h t => s!"{h.toLean} :: {t.toLean}"
  | .append l r => s!"{l.toLean} ++ {r.toLean}"
  | .dot recv method =>
    s!"{recv.toLean}.{method}"
  | .flatMap list param body =>
    s!"{list.toLean}.flatMap fun {param} => \
       {body.toLean}"
  | .field recv name => s!"{recv.toLean}.{name}"
  | .index list idx =>
    s!"{list.toLean}[{idx.toLean}]?"
  | .call fn args =>
    let argStr := " ".intercalate (args.map toLeanArg)
    s!"{fn} {argStr}"
  | .foldlM fn init list =>
    s!"{list.toLean}.foldlM {fn} {init.toLean}"
end

end BodyExpr

namespace BodyStmt

def toLean : BodyStmt → String
  | .let_ n v => s!"  let {n} := {v.toLean}"
  | .letBind n v => s!"  let {n} ← {v.toLean}"

end BodyStmt

namespace FnBody

def toLean : FnBody → String
  | .matchArms arms =>
    "\n".intercalate (arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map BodyPat.toLean)
      s!"  | {patStr} => {arm.rhs.toLean}")
  | .doBlock stmts ret =>
    let stmtStrs := stmts.map BodyStmt.toLean
    let all := stmtStrs ++ [s!"  {ret.toLean}"]
    " do\n".intercalate [] ++ "\n".intercalate all

end FnBody
