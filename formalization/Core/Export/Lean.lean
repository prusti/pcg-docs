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
  | .map k v => .app2 "Std.HashMap" k.toLeanAST v.toLeanAST
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
  | .map k v => k.namedTypes ++ v.namedTypes
  | .tuple ts => ts.flatMap namedTypes

/-- Whether this type uses `Set`. -/
partial def usesSet : DSLType → Bool
  | .set _ => true
  | .option t => t.usesSet
  | .list t => t.usesSet
  | .map k v => k.usesSet || v.usesSet
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
-- DslExpr → LeanExpr
-- ══════════════════════════════════════════════

namespace DslExpr

/-- Algebra for `toLeanASTWith`: recursive children have already been
    lowered to `LeanExpr`. `selfName` and `precondNames` drive insertion of
    precondition proof arguments at recursive calls; `calleeProofNames`
    lists callees requiring `sorry` arguments. `proofArgs` is the precomputed
    list of precondition proof terms (rendered as `raw` to bypass the
    atomic-arg re-parenthesisation logic in `LeanExpr.toAtom`). -/
private def toLeanASTAlg
    (selfName : String) (precondNames : List String)
    (calleeProofNames : List String) (proofArgs : List LeanExpr) :
    DslExprF LeanExpr → LeanExpr
  | .var n => .ident n
  | .natLit n => .natLit n
  | .true_ => .boolLit true
  | .false_ => .boolLit false
  | .emptyList => .listNil
  | .none_ => .noneE
  | .some_ e => .someE e
  | .mkStruct _ args => .anonCtor args
  | .cons h t => .listCons h t
  | .append l r => .listAppend l r
  | .dot recv method => .dot recv method []
  | .flatMap list param body => .listFlatMap list param body
  | .map list param body => .listMap list param body
  | .mapFn list fn => .listMapFn list fn
  | .field recv name => .field recv name
  | .index list idx => .index list idx
  | .indexBang list idx => .indexBang list idx
  | .call fn args =>
    if fn == selfName && !precondNames.isEmpty then
      .app fn (args ++ proofArgs)
    else if calleeProofNames.contains fn then
      .app fn (args ++ [.raw "sorry"])
    else
      .app fn args
  | .foldlM fn init list => .foldlM list fn init
  | .lt l r => .binop "<" l r
  | .le l r => .binop "≤" l r
  | .ltChain es => .ltChain es
  | .leChain es => .leChain es
  | .add l r => .binop "+" l r
  | .sub l r => .binop "-" l r
  | .div l r => .binop "/" l r
  | .setAll set param body => .forallIn param set body
  | .emptySet => .emptySet
  | .setSingleton e => .app "Set.singleton" [e]
  | .setUnion l r => .listAppend l r
  | .setFlatMap list param body => .setFlatMapList list param body
  | .and l r => .binop "∧" l r
  | .or l r => .binop "∨" l r
  | .implies l r => .binop "→" l r
  | .forall_ p b => .forall_ p b
  | .sorryProof => .raw "sorry"
  | .leanProof t => .raw t
  | .match_ scrut arms =>
    .match_ scrut <| arms.map fun (pats, rhs) =>
      .mk (pats.map BodyPat.toLeanAST) rhs
  | .letIn name val body => .letIn name val body
  | .letBindIn name val body => .letBindIn name val body
  | .ifThenElse c t e => .ifThenElse c t e
  | .neq l r => .binop "≠" l r

/-- Lower a `DslExpr` to a `LeanExpr`.
    `selfName` is the current function name (for
    inserting proof arguments at recursive calls).
    `precondNames` lists the precondition function
    names. `calleeProofNames` lists callee functions
    that also require sorry proof arguments. -/
def toLeanASTWith
    (selfName : String)
    (precondNames : List String)
    (calleeProofNames : List String := [])
    (e : DslExpr) : LeanExpr :=
  let proofArgs : List LeanExpr :=
    precondNames.map fun pn =>
      .raw s!"(by simp_all [{pn}])"
  DslExpr.cata
    (toLeanASTAlg selfName precondNames calleeProofNames proofArgs) e

partial def toLeanAST (e : DslExpr) : LeanExpr :=
  e.toLeanASTWith "" []

partial def toLeanWith
    (selfName : String)
    (precondNames : List String)
    (calleeProofNames : List String := [])
    (e : DslExpr) : String :=
  toString (e.toLeanASTWith selfName precondNames
    calleeProofNames)

partial def toLean (e : DslExpr) : String :=
  toString e.toLeanAST

partial def toLeanArg (e : DslExpr) : String :=
  LeanExpr.toAtom e.toLeanAST

end DslExpr

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

namespace DslExpr

/-- Algebra for `calledNames`: children are already the collected names of
    sub-expressions. -/
private def calledNamesAlg : DslExprF (List String) → List String
  | .var _ | .natLit _ | .true_ | .false_ | .emptyList | .none_
  | .emptySet | .sorryProof | .leanProof _ => []
  | .some_ e => e
  | .mkStruct _ args => args.flatten
  | .cons h t => h ++ t
  | .append l r => l ++ r
  | .dot _ method => [method]
  | .flatMap list _ body => list ++ body
  | .map list _ body => list ++ body
  | .mapFn list fn => fn :: list
  | .field e _ => e
  | .index l i => l ++ i
  | .indexBang l i => l ++ i
  | .call fn args => fn :: args.flatten
  | .foldlM fn init list => fn :: init ++ list
  | .lt l r => l ++ r
  | .le l r => l ++ r
  | .ltChain es => es.flatten
  | .leChain es => es.flatten
  | .add l r => l ++ r
  | .sub l r => l ++ r
  | .div l r => l ++ r
  | .setAll set _ body => set ++ body
  | .setSingleton e => e
  | .setUnion l r => l ++ r
  | .setFlatMap list _ body => list ++ body
  | .and l r => l ++ r
  | .or l r => l ++ r
  | .implies l r => l ++ r
  | .forall_ _ b => b
  | .match_ scrut arms =>
    scrut ++ arms.flatMap (fun (_, rhs) => rhs)
  | .letIn _ v b => v ++ b
  | .letBindIn _ v b => v ++ b
  | .ifThenElse c t e => c ++ t ++ e
  | .neq l r => l ++ r

/-- Collect all function/method names called. -/
def calledNames (e : DslExpr) : List String :=
  DslExpr.cata calledNamesAlg e

end DslExpr

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
