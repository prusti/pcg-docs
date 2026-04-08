import Core.Dsl.DslType
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.PropertyDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.LeanAST

open LeanAST

-- ══════════════════════════════════════════════
-- DSLPrimTy / DSLType → LeanAST
-- ══════════════════════════════════════════════

namespace DSLPrimTy

/-- Lower a primitive type to a `LeanTy`. -/
def toLeanAST : DSLPrimTy → LeanTy
  | .nat => .const "Nat"
  | .string => .const "String"
  | .bool => .const "Bool"
  | .unit => .const "Unit"
  | .u8 => .const "UInt8"
  | .u16 => .const "UInt16"
  | .u32 => .const "UInt32"
  | .u64 => .const "UInt64"
  | .usize => .const "USize"

/-- Render a primitive to Lean syntax. -/
def toLean (p : DSLPrimTy) : String :=
  toString p.toLeanAST

end DSLPrimTy

namespace DSLType

/-- Lower a `DSLType` to a `LeanTy`. -/
partial def toLeanAST : DSLType → LeanTy
  | .prim p => p.toLeanAST
  | .named n => .const n.name
  | .option t => .app "Option" t.toLeanAST
  | .list t => .app "List" t.toLeanAST
  | .set t => .app "Set" t.toLeanAST
  | .tuple ts => .product (ts.map toLeanAST)

/-- Render a type to Lean syntax. -/
partial def toLean (t : DSLType) : String :=
  toString t.toLeanAST

/-- Collect all named type references. -/
partial def namedTypes : DSLType → List String
  | .prim _ => []
  | .named n => [n.name]
  | .option t => t.namedTypes
  | .list t => t.namedTypes
  | .set t => t.namedTypes
  | .tuple ts => ts.flatMap namedTypes

/-- Whether this type uses `Set`. -/
partial def usesSet : DSLType → Bool
  | .set _ => true
  | .option t => t.usesSet
  | .list t => t.usesSet
  | .tuple ts => ts.any usesSet
  | _ => false

end DSLType

namespace FieldDef

/-- Backward-compatible accessor. -/
def typeName (f : FieldDef) : String :=
  f.ty.toLean

end FieldDef

-- ══════════════════════════════════════════════
-- BodyPat → LeanPat
-- ══════════════════════════════════════════════

namespace BodyPat

partial def toLeanAST : BodyPat → LeanPat
  | .wild => .wild
  | .var n => .var n
  | .ctor "⟨⟩" args => .anonCtor (args.map toLeanAST)
  | .ctor n args => .ctor n (args.map toLeanAST)
  | .nil => .listNil
  | .cons h t => .listCons h.toLeanAST t.toLeanAST
  | .natLit n => .natLit n

partial def toLean (p : BodyPat) : String :=
  toString p.toLeanAST

end BodyPat

-- ══════════════════════════════════════════════
-- BodyExpr → LeanExpr
-- ══════════════════════════════════════════════

namespace BodyExpr

/-- Lower a `BodyExpr` to a `LeanExpr`.
    `selfName` is the current function name (for
    inserting proof arguments at recursive calls).
    `precondNames` lists the precondition function
    names. `calleeProofNames` lists callee functions
    that also require sorry proof arguments. -/
partial def toLeanASTWith
    (selfName : String)
    (precondNames : List String)
    (calleeProofNames : List String := [])
    : BodyExpr → LeanExpr :=
  let go := toLeanASTWith selfName precondNames
    calleeProofNames
  -- For self-recursive calls we need to attach
  -- precondition proof terms; for known callees we
  -- attach `sorry`. We render these as `raw` so the
  -- atomic-arg logic in `LeanExpr.toAtom` doesn't
  -- accidentally re-parenthesize them.
  let proofArgs : List LeanExpr :=
    precondNames.map fun pn =>
      .raw s!"(by simp_all [{pn}])"
  fun
  | .var n => .ident n
  | .natLit n => .natLit n
  | .true_ => .boolLit true
  | .false_ => .boolLit false
  | .emptyList => .listNil
  | .none_ => .noneE
  | .some_ e => .someE (go e)
  | .mkStruct _ args => .anonCtor (args.map go)
  | .cons h t => .listCons (go h) (go t)
  | .append l r => .listAppend (go l) (go r)
  | .dot recv method => .dot (go recv) method []
  | .flatMap list param body =>
    .listFlatMap (go list) param (go body)
  | .field recv name => .field (go recv) name
  | .index list idx => .index (go list) (go idx)
  | .indexBang list idx => .indexBang (go list) (go idx)
  | .call fn args =>
    let argEs := args.map go
    if fn == selfName && !precondNames.isEmpty then
      .app fn (argEs ++ proofArgs)
    else if calleeProofNames.contains fn then
      .app fn (argEs ++ [.raw "sorry"])
    else
      .app fn argEs
  | .foldlM fn init list =>
    .foldlM (go list) fn (go init)
  | .lt l r => .binop "<" (go l) (go r)
  | .le l r => .binop "≤" (go l) (go r)
  | .ltChain es => .ltChain (es.map go)
  | .add l r => .binop "+" (go l) (go r)
  | .sub l r => .binop "-" (go l) (go r)
  | .setAll set param body =>
    .forallIn param (go set) (go body)
  | .emptySet => .emptySet
  | .setSingleton e => .app "Set.singleton" [go e]
  | .setUnion l r => .listAppend (go l) (go r)
  | .setFlatMap list param body =>
    .setFlatMapList (go list) param (go body)
  | .and l r => .binop "∧" (go l) (go r)
  | .implies l r => .binop "→" (go l) (go r)
  | .forall_ p b => .forall_ p (go b)
  | .sorryProof => .raw "sorry"
  | .leanProof t => .raw t
  | .match_ scrut arms =>
    .match_ (go scrut) <| arms.map fun (pats, rhs) =>
      .mk (pats.map BodyPat.toLeanAST) (go rhs)
  | .letIn name val body =>
    .letIn name (go val) (go body)
  | .letBindIn name val body =>
    .letBindIn name (go val) (go body)

partial def toLeanAST (e : BodyExpr) : LeanExpr :=
  e.toLeanASTWith "" []

partial def toLeanWith
    (selfName : String)
    (precondNames : List String)
    (calleeProofNames : List String := [])
    (e : BodyExpr) : String :=
  toString (e.toLeanASTWith selfName precondNames
    calleeProofNames)

partial def toLean (e : BodyExpr) : String :=
  toString e.toLeanAST

partial def toLeanArg (e : BodyExpr) : String :=
  LeanExpr.toAtom e.toLeanAST

end BodyExpr

-- ══════════════════════════════════════════════
-- FnBody (rendered standalone, e.g. in DefFn)
-- ══════════════════════════════════════════════

namespace FnBody

def toLean : FnBody → String
  | .matchArms arms => arms.foldl
    (fun acc arm =>
      let patStr := ", ".intercalate
        (arm.pat.map BodyPat.toLean)
      let rhsStr := arm.rhs.toLean
      acc ++ s!"  | {patStr} => {rhsStr}\n") ""
  | .expr body => s!"  {body.toLean}\n"

end FnBody

-- ══════════════════════════════════════════════
-- StructDef / EnumDef → LeanDecl
-- ══════════════════════════════════════════════

namespace StructDef

/-- Lower a struct definition to a `LeanDecl`. -/
def toLeanAST (s : StructDef) : LeanDecl :=
  .structure_ s.name <| s.fields.map fun f =>
    { name := f.name, type := f.ty.toLeanAST }

/-- Render a struct definition to Lean syntax. -/
def toLean (s : StructDef) : String :=
  toString s.toLeanAST

end StructDef

namespace EnumDef

/-- Lower an enum definition to an `inductive` declaration. -/
def toLeanAST (e : EnumDef) : LeanDecl :=
  .inductive_ e.name.name <| e.variants.map fun v =>
    { name := v.name.name
      args := v.args.map fun a =>
        { name := a.name, type := a.type.toLeanAST } }

/-- Render an enum definition to a Lean `inductive`. -/
def toLean (e : EnumDef) : String :=
  toString e.toLeanAST

end EnumDef

-- ══════════════════════════════════════════════
-- FnDef / PropertyDef → LeanDecl
-- ══════════════════════════════════════════════

/-- Build precondition binders for a generated def. Each
    `prop(a, b)` becomes `(h_prop : prop a b)`. -/
private def precondBinders
    (preconds : List Precondition) : List LeanBinder :=
  preconds.map fun pc =>
    let argStr := " ".intercalate pc.args
    { name := s!"h_{pc.name}"
      type := .const s!"{pc.name} {argStr}" }

/-- Convert FnDef params to AST binders. -/
private def paramBinders
    (params : List FieldDef) : List LeanBinder :=
  params.map fun p =>
    { name := p.name, type := p.ty.toLeanAST }

namespace FnDef

/-- Lower a function definition to a `LeanDecl`.
    If `isProperty` is true, the return type is `Prop`
    and a catch-all `False` arm is appended for
    pattern-matching bodies that don't already have one. -/
def toLeanAST
    (f : FnDef)
    (isProperty : Bool := false)
    : LeanDecl :=
  let precondNames := f.preconditions.map (·.name)
  let retType : LeanTy :=
    if isProperty then .const "Prop"
    else f.returnType.toLeanAST
  let params := paramBinders f.params
  let precBinds := precondBinders f.preconditions
  let body : LeanFnBody :=
    match f.body with
    | .matchArms arms =>
      let armASTs : List LeanMatchArm := arms.map fun arm =>
        .mk (arm.pat.map BodyPat.toLeanAST)
            (arm.rhs.toLeanASTWith f.name precondNames)
      let lastIsCatchAll := match arms.getLast? with
        | some arm => arm.pat.all fun p =>
            match p with | .wild | .var _ => true | _ => false
        | none => false
      let armASTs :=
        if isProperty && !lastIsCatchAll then
          let wildPats := f.params.map fun _ => LeanPat.wild
          armASTs ++ [.mk wildPats (.ident "False")]
        else armASTs
      .matchArms armASTs
    | .expr body =>
      .expr (body.toLeanASTWith f.name precondNames)
  .def_ {
    name := f.name
    params
    precondBinds := precBinds
    retType
    body
    doRequiresProof := !f.preconditions.isEmpty
  }

/-- Render a function definition to Lean syntax. -/
def toLean
    (f : FnDef) (isProperty : Bool := false) : String :=
  toString (f.toLeanAST isProperty)

end FnDef

namespace PropertyDef

/-- Lower a property to a `LeanDecl`. -/
def toLeanAST (p : PropertyDef) : LeanDecl :=
  p.fnDef.toLeanAST (isProperty := true)

/-- Render a property definition to Lean syntax. -/
def toLean (p : PropertyDef) : String :=
  toString p.toLeanAST

end PropertyDef

-- ══════════════════════════════════════════════
-- Type-name extraction for import computation
-- ══════════════════════════════════════════════

namespace StructDef

/-- All named types referenced by this struct. -/
def referencedTypes (s : StructDef) : List String :=
  s.fields.flatMap fun f => f.ty.namedTypes

/-- Whether this struct uses `Set` anywhere. -/
def usesSet (s : StructDef) : Bool :=
  s.fields.any fun f => f.ty.usesSet

end StructDef

namespace EnumDef

/-- All named types referenced by this enum. -/
def referencedTypes (e : EnumDef) : List String :=
  e.variants.flatMap fun v =>
    v.args.flatMap fun a => a.type.namedTypes

/-- Whether this enum uses `Set` anywhere. -/
def usesSet (e : EnumDef) : Bool :=
  e.variants.any fun v =>
    v.args.any fun a => a.type.usesSet

end EnumDef

namespace BodyExpr

/-- Collect all function/method names called. -/
partial def calledNames : BodyExpr → List String
  | .dot _ method => [method]
  | .call fn args =>
    fn :: args.flatMap calledNames
  | .foldlM fn init list =>
    fn :: init.calledNames ++ list.calledNames
  | .setAll set _ body =>
    set.calledNames ++ body.calledNames
  | .setFlatMap list _ body =>
    list.calledNames ++ body.calledNames
  | .flatMap list _ body =>
    list.calledNames ++ body.calledNames
  | .and l r => l.calledNames ++ r.calledNames
  | .implies l r => l.calledNames ++ r.calledNames
  | .forall_ _ b => b.calledNames
  | .setUnion l r => l.calledNames ++ r.calledNames
  | .append l r => l.calledNames ++ r.calledNames
  | .some_ e => e.calledNames
  | .setSingleton e => e.calledNames
  | .cons h t => h.calledNames ++ t.calledNames
  | .lt l r => l.calledNames ++ r.calledNames
  | .le l r => l.calledNames ++ r.calledNames
  | .ltChain es => es.flatMap calledNames
  | .add l r => l.calledNames ++ r.calledNames
  | .sub l r => l.calledNames ++ r.calledNames
  | .mkStruct _ args => args.flatMap calledNames
  | .index l i => l.calledNames ++ i.calledNames
  | .indexBang l i => l.calledNames ++ i.calledNames
  | .field e _ => e.calledNames
  | .match_ scrut arms =>
    scrut.calledNames ++
      arms.flatMap fun (_, rhs) => rhs.calledNames
  | .letIn _ v b => v.calledNames ++ b.calledNames
  | .letBindIn _ v b => v.calledNames ++ b.calledNames
  | _ => []

end BodyExpr

namespace FnBody

/-- Collect all function/method names called. -/
def calledNames : FnBody → List String
  | .matchArms arms =>
    arms.flatMap fun a => a.rhs.calledNames
  | .expr body => body.calledNames

end FnBody

namespace FnDef

/-- All named types referenced by this function. -/
def referencedTypes (f : FnDef) : List String :=
  f.returnType.namedTypes ++
  f.params.flatMap fun p => p.ty.namedTypes

/-- All names this function depends on (types,
    preconditions, called functions). -/
def referencedNames (f : FnDef) : List String :=
  f.referencedTypes ++
  f.preconditions.map (·.name) ++
  f.body.calledNames

/-- Whether this function uses `Set` anywhere. -/
def usesSet (f : FnDef) : Bool :=
  f.returnType.usesSet ||
  f.params.any fun p => p.ty.usesSet

end FnDef
