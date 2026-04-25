import Core.Dsl.DslType
import Core.Dsl.Types.AliasDef
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.PropertyDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.InductivePropertyDef
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
  | .app h args => .appN h.name (args.map toLeanAST)
  | .option t => .app "Option" t.toLeanAST
  | .list t => .app "List" t.toLeanAST
  | .set t => .app "Set" t.toLeanAST
  | .map k v => .app2 "Std.HashMap" k.toLeanAST v.toLeanAST
  | .tuple ts => .product (ts.map toLeanAST)
  | .arrow a b => .arrow a.toLeanAST b.toLeanAST

/-- Render a type to Lean syntax. -/
partial def toLean (t : DSLType) : String :=
  toString t.toLeanAST

/-- Collect all named type references. -/
partial def namedTypes : DSLType → List String
  | .prim _ => []
  | .named n => [n.name]
  | .app h args => h.name :: args.flatMap namedTypes
  | .option t => t.namedTypes
  | .list t => t.namedTypes
  | .set t => t.namedTypes
  | .map k v => k.namedTypes ++ v.namedTypes
  | .tuple ts => ts.flatMap namedTypes
  | .arrow a b => a.namedTypes ++ b.namedTypes

/-- Whether this type uses `Set`. -/
partial def usesSet : DSLType → Bool
  | .set _ => true
  | .app _ args => args.any usesSet
  | .option t => t.usesSet
  | .list t => t.usesSet
  | .map k v => k.usesSet || v.usesSet
  | .tuple ts => ts.any usesSet
  | .arrow a b => a.usesSet || b.usesSet
  | _ => false

/-- Whether this type uses `Map`. -/
partial def usesMap : DSLType → Bool
  | .map _ _ => true
  | .app _ args => args.any usesMap
  | .option t => t.usesMap
  | .list t => t.usesMap
  | .set t => t.usesMap
  | .tuple ts => ts.any usesMap
  | .arrow a b => a.usesMap || b.usesMap
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
  | .lambda param body => .lambda param.name body
  | .flatMap list fn => .dot list "flatMap" [fn]
  | .map list fn => .dot list "map" [fn]
  | .field recv name => .field recv name
  | .index list idx => .index list idx
  | .indexBang list idx => .indexBang list idx
  | .call fn args =>
    let fnName := match fn with
      | .ident n => n | _ => fn.toString
    if fnName == selfName && !precondNames.isEmpty then
      .app fnName (args ++ proofArgs)
    else if calleeProofNames.contains fnName then
      .app fnName (args ++ [.raw "sorry"])
    else
      .app fnName args
  | .foldlM fn init list =>
    let fnName := match fn with
      | .ident n => n | _ => fn.toString
    .foldlM list fnName init
  | .lt l r => .binop "<" l r
  | .le l r => .binop "≤" l r
  | .ineqChain ops es => .ineqChain ops es
  | .add l r => .binop "+" l r
  | .sub l r => .binop "-" l r
  | .mul l r => .binop "*" l r
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
  | .letIn name val body => .letIn name.name val body
  | .letBindIn name val body => .letBindIn name val body
  | .ifThenElse c t e => .ifThenElse c t e
  | .neq l r => .binop "≠" l r
  | .eq l r => .binop "==" l r
  | .memberOf l r => .binop "∈" l r
  | .anyList list param body =>
    -- `list.any (fun param => body)` in Lean.
    .dot list "any" [.lambda param body]
  | .structUpdate recv fieldName value =>
    .recordUpdate recv fieldName value

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

/-- Lower a struct definition to a `LeanDecl`. `mapSetTypes`
    names struct types that transitively hold a `Map`/`Set`;
    any field referencing one such type is flagged via
    `LeanField.usesMapSet` so the renderer can suppress
    `BEq`/`Hashable` derives. -/
def toLeanASTWith (s : StructDef)
    (mapSetTypes : List String) : LeanDecl :=
  .structure_ s.name s.typeParams <| s.fields.map fun f =>
    let fieldUsesMapSet :=
      f.ty.usesMap || f.ty.usesSet ||
      f.ty.namedTypes.any (fun n => mapSetTypes.contains n)
    { name := f.name, type := f.ty.toLeanAST,
      usesMapSet := fieldUsesMapSet }

/-- Lower a struct definition to a `LeanDecl`. -/
def toLeanAST (s : StructDef) : LeanDecl :=
  s.toLeanASTWith []

/-- Render a struct definition to Lean syntax. -/
def toLean (s : StructDef) : String :=
  toString s.toLeanAST

end StructDef

namespace AliasDef

/-- Lower a type alias to a Lean `abbrev` declaration. -/
def toLeanAST (a : AliasDef) : LeanDecl :=
  .abbrev_ a.name a.typeParams a.aliased.toLeanAST

/-- Render a type alias to Lean source. -/
def toLean (a : AliasDef) : String :=
  toString a.toLeanAST

end AliasDef

namespace EnumDef

/-- Lower an enum definition to an `inductive` declaration. -/
def toLeanAST (e : EnumDef) : LeanDecl :=
  .inductive_ e.name.name e.typeParams <|
    e.variants.map fun v =>
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

namespace InductivePropertyDef

/-- All named types referenced by the parameters of an
    inductive property. The rule premises and conclusion are
    opaque Lean source strings and are not analysed here. -/
def referencedTypes (p : InductivePropertyDef) : List String :=
  p.params.flatMap fun f => f.ty.namedTypes

/-- Whether this inductive property uses `Set` anywhere in
    its parameter types (always false for the rule terms,
    which are opaque). -/
def usesSet (p : InductivePropertyDef) : Bool :=
  p.params.any fun f => f.ty.usesSet

/-- Lower an inductive-property definition to a
    `LeanDecl.raw_` carrying the precomputed Lean source for
    the underlying `inductive Name … : Prop where | …`
    declaration. -/
def toLeanAST (p : InductivePropertyDef) : LeanDecl :=
  .raw_ p.leanSource

/-- Render an inductive-property definition to Lean source
    (just the precomputed declaration). -/
def toLean (p : InductivePropertyDef) : String :=
  toString p.toLeanAST

end InductivePropertyDef

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

namespace AliasDef

/-- All named types referenced by the alias body. -/
def referencedTypes (a : AliasDef) : List String :=
  a.aliased.namedTypes

/-- Whether the alias body uses `Set` anywhere. -/
def usesSet (a : AliasDef) : Bool := a.aliased.usesSet

end AliasDef

namespace DslExpr

/-- Algebra for `calledNames` (via `para`): each recursive child
    is a pair `(originalExpr, collectedNames)`. We need the
    original for `.call` and `.foldlM` where the function is now
    a `DslExpr` and we must extract the name when it is a `.var`. -/
private def calledNamesAlg :
    DslExprF (DslExpr × List String) → List String
  | .var _ | .natLit _ | .true_ | .false_ | .emptyList | .none_
  | .emptySet | .sorryProof | .leanProof _ => []
  | .some_ (_, e) => e
  | .lambda _ (_, body) => body
  | .mkStruct _ args => (args.map Prod.snd).flatten
  | .cons (_, h) (_, t) => h ++ t
  | .append (_, l) (_, r) => l ++ r
  | .dot _ method => [method]
  | .flatMap (_, list) (origFn, fn) =>
    let fnNames := match origFn with
      | .var n => [n] | _ => fn
    list ++ fnNames
  | .map (_, list) (origFn, fn) =>
    let fnNames := match origFn with
      | .var n => [n] | _ => fn
    list ++ fnNames
  | .field (_, e) _ => e
  | .index (_, l) (_, i) => l ++ i
  | .indexBang (_, l) (_, i) => l ++ i
  | .call (origFn, _) args =>
    let fnName := match origFn with
      | .var n => [n] | _ => []
    fnName ++ (args.map Prod.snd).flatten
  | .foldlM (origFn, _) (_, init) (_, list) =>
    let fnName := match origFn with
      | .var n => [n] | _ => []
    fnName ++ init ++ list
  | .lt (_, l) (_, r) => l ++ r
  | .le (_, l) (_, r) => l ++ r
  | .ineqChain _ es => (es.map Prod.snd).flatten
  | .add (_, l) (_, r) => l ++ r
  | .sub (_, l) (_, r) => l ++ r
  | .mul (_, l) (_, r) => l ++ r
  | .div (_, l) (_, r) => l ++ r
  | .setAll (_, set) _ (_, body) => set ++ body
  | .setSingleton (_, e) => e
  | .setUnion (_, l) (_, r) => l ++ r
  | .setFlatMap (_, list) _ (_, body) => list ++ body
  | .and (_, l) (_, r) => l ++ r
  | .or (_, l) (_, r) => l ++ r
  | .implies (_, l) (_, r) => l ++ r
  | .forall_ _ (_, b) => b
  | .match_ (_, scrut) arms =>
    scrut ++ arms.flatMap (fun (_, (_, rhs)) => rhs)
  | .letIn _ (_, v) (_, b) => v ++ b
  | .letBindIn _ (_, v) (_, b) => v ++ b
  | .ifThenElse (_, c) (_, t) (_, e) => c ++ t ++ e
  | .neq (_, l) (_, r) => l ++ r
  | .eq (_, l) (_, r) => l ++ r
  | .memberOf (_, l) (_, r) => l ++ r
  | .anyList (_, l) _ (_, b) => l ++ b
  | .structUpdate (_, recv) _ (_, value) => recv ++ value

/-- Collect all function/method names called. -/
def calledNames (e : DslExpr) : List String :=
  DslExpr.para calledNamesAlg e

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
