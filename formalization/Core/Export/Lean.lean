import Core.Dsl.DslType
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.StructDef

-- ══════════════════════════════════════════════
-- Lean rendering for DSLPrimTy / DSLType
-- ══════════════════════════════════════════════

namespace DSLPrimTy

/-- Render a primitive to Lean syntax. -/
def toLean : DSLPrimTy → String
  | .nat => "Nat"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "Unit"
  | .u8 => "UInt8"
  | .u16 => "UInt16"
  | .u32 => "UInt32"
  | .u64 => "UInt64"
  | .usize => "USize"

end DSLPrimTy

namespace DSLType

/-- Render a type to Lean syntax. -/
def toLean : DSLType → String
  | .prim p => p.toLean
  | .named n => n.name
  | .option t => s!"Option {t.toLean}"
  | .list t => s!"List {t.toLean}"
  | .set t => s!"Set {t.toLean}"

end DSLType

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
    else
      let argStr := " ".intercalate
        (args.map fun a => match a with
          | .wild => "_" | .var v => v
          | _ => s!"({a.toLean})")
      s!".{n} {argStr}"
  | .nil => "[]"
  | .cons h t => s!"{h.toLean} :: {t.toLean}"

end BodyPat

namespace BodyExpr

/-- Render a `BodyExpr` to Lean syntax.
    `selfName` is the current function name (for
    inserting proof arguments at recursive calls).
    `precondNames` lists the precondition function
    names. `calleeProofNames` lists callee functions
    that also require sorry proof arguments. -/
partial def toLeanWith
    (selfName : String)
    (precondNames : List String)
    (calleeProofNames : List String := [])
    : BodyExpr → String :=
  let go := toLeanWith selfName precondNames
    calleeProofNames
  let goArg (e : BodyExpr) : String :=
    match e with
    | .var n => n | .true_ => "true"
    | .false_ => "false" | .none_ => "none"
    | .emptyList => "[]"
    | .emptySet => "(∅ : Set _)"
    | e => s!"({go e})"
  let proofArgs :=
    " ".intercalate
      (precondNames.map fun pn =>
        s!"(by simp_all [{pn}])")
  fun
  | .var n => n
  | .true_ => "true"
  | .false_ => "false"
  | .emptyList => "[]"
  | .none_ => "none"
  | .some_ e => s!"some {go e}"
  | .mkStruct _ args =>
    s!"⟨{", ".intercalate (args.map go)}⟩"
  | .cons h t => s!"{go h} :: {go t}"
  | .append l r => s!"{go l} ++ {go r}"
  | .dot recv "toSet" =>
    s!"{go recv}.toSet"
  | .dot recv method =>
    s!"{go recv}.{method}"
  | .flatMap list param body =>
    s!"{go list}.flatMap fun {param} => \
       {go body}"
  | .field recv name => s!"{go recv}.{name}"
  | .index list idx =>
    s!"{go list}[{go idx}]?"
  | .indexBang list idx =>
    s!"{go list}[{go idx}]!"
  | .call fn args =>
    let argStr := " ".intercalate (args.map goArg)
    if fn == selfName && !precondNames.isEmpty then
      s!"{fn} {argStr} {proofArgs}"
    else if calleeProofNames.contains fn then
      s!"{fn} {argStr} sorry"
    else s!"{fn} {argStr}"
  | .foldlM fn init list =>
    s!"{go list}.foldlM {fn} {go init}"
  | .lt l r => s!"{go l} < {go r}"
  | .setAll set param body =>
    s!"∀ {param} ∈ {go set}, {go body}"
  | .emptySet => "(∅ : Set _)"
  | .setSingleton e =>
    s!"Set.singleton {goArg e}"
  | .setUnion l r =>
    s!"{go l} ++ {go r}"
  | .setFlatMap list param body =>
    s!"Set.flatMapList {goArg list} fun {param} => \
       {go body}"
  | .and l r => s!"{go l} ∧ {go r}"
  | .sorryProof => "sorry"

partial def toLean : BodyExpr → String :=
  toLeanWith "" []

partial def toLeanArg : BodyExpr → String
  | .var n => n
  | .true_ => "true"
  | .false_ => "false"
  | .none_ => "none"
  | .emptyList => "[]"
  | .emptySet => "(∅ : Set _)"
  | e => s!"({e.toLean})"

end BodyExpr

namespace BodyStmt

def toLean : BodyStmt → String
  | .let_ n v => s!"  let {n} := {v.toLean}"
  | .letBind n v => s!"  let {n} ← {v.toLean}"

end BodyStmt

namespace FnBody

def toLean : FnBody → String
  | .matchArms arms => arms.foldl
    (fun acc arm =>
      let patStr := ", ".intercalate
        (arm.pat.map BodyPat.toLean)
      let rhsStr := arm.rhs.toLean
      acc ++ s!"  | {patStr} => {rhsStr}\n") ""
  | .doBlock stmts ret =>
    let body := stmts.map BodyStmt.toLean
    let retStr := ret.toLean
    (body ++ [s!"  {retStr}"]).foldl
      (fun acc l => acc ++ l ++ "\n") ""

end FnBody
