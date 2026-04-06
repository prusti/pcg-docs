import Core.Dsl.DslType
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.PropertyDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef

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

/-- Collect all named type references. -/
def namedTypes : DSLType → List String
  | .prim _ => []
  | .named n => [n.name]
  | .option t => t.namedTypes
  | .list t => t.namedTypes
  | .set t => t.namedTypes

/-- Whether this type uses `Set`. -/
def usesSet : DSLType → Bool
  | .set _ => true
  | .option t => t.usesSet
  | .list t => t.usesSet
  | _ => false

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
  | .natLit n => toString n
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
    s!"{goArg recv}.toSet"
  | .dot recv method =>
    s!"{goArg recv}.{method}"
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
  | .le l r => s!"{go l} ≤ {go r}"
  | .ltChain es =>
    let pairs := es.zip (es.drop 1)
    " ∧ ".intercalate
      (pairs.map fun (l, r) => s!"{go l} < {go r}")
  | .add l r => s!"{go l} + {go r}"
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
  | .implies l r => s!"{go l} → {go r}"
  | .forall_ p b => s!"∀ {p}, {go b}"
  | .sorryProof => "sorry"
  | .leanProof t => t

partial def toLean : BodyExpr → String :=
  toLeanWith "" []

partial def toLeanArg : BodyExpr → String
  | .var n => n
  | .natLit n => toString n
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
  | .expr body => s!"  {body.toLean}\n"

end FnBody

-- ═══════���════════════════════════��═════════════
-- Definition-level Lean rendering
-- ══════════════════════════════════════════════

namespace StructDef

/-- Render a struct definition to Lean syntax. -/
def toLean (s : StructDef) : String :=
  let fieldStrs := s.fields.map fun f =>
    s!"  {f.name} : {f.ty.toLean}"
  s!"structure {s.name} where\n\
     {"\n".intercalate fieldStrs}\n\
     deriving Repr, BEq, Hashable, Inhabited"

end StructDef

namespace EnumDef

/-- Render an enum definition to a Lean `inductive`. -/
def toLean (e : EnumDef) : String :=
  let variantStrs := e.variants.map fun v =>
    let argStr := v.args.map fun a =>
      s!"({a.name} : {a.type.toLean})"
    if argStr.isEmpty then s!"  | {v.name.name}"
    else s!"  | {v.name.name} {" ".intercalate argStr}"
  s!"inductive {e.name.name} where\n\
     {"\n".intercalate variantStrs}\n\
     deriving Repr, BEq, Hashable, Inhabited"

end EnumDef

/-- Build precondition parameter bindings for a
    generated Lean def. Each precondition `prop(a, b)`
    becomes `(h_prop : prop a b)`. -/
private def precondParamBinds
    (preconds : List Precondition) : String :=
  " ".intercalate
    (preconds.map fun pc =>
      let argStr := " ".intercalate pc.args
      s!"(h_{pc.name} : {pc.name} {argStr})")

namespace FnDef

/-- Render a function definition to Lean syntax. -/
def toLean
    (f : FnDef)
    (isProperty : Bool := false)
    : String :=
  let precondNames := f.preconditions.map (·.name)
  let paramBinds := " ".intercalate
    (f.params.map fun p =>
      s!"({p.name} : {p.ty.toLean})")
  let retRepr :=
    if isProperty then "Prop"
    else f.returnType.toLean
  let precBinds := precondParamBinds f.preconditions
  match f.body with
  | .matchArms arms =>
    let armStrs := arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map BodyPat.toLean)
      let rhsStr := arm.rhs.toLeanWith
        f.name precondNames
      s!"  | {patStr} => {rhsStr}"
    let lastIsCatchAll := match arms.getLast? with
      | some arm => arm.pat.all fun p =>
          match p with | .wild | .var _ => true | _ => false
      | none => false
    let armStrs :=
      if isProperty && !lastIsCatchAll then
        let wildPat := ", ".intercalate
          (f.params.map fun _ => "_")
        armStrs ++ [s!"  | {wildPat} => False"]
      else armStrs
    if f.preconditions.isEmpty then
      let tyStr := " → ".intercalate
        (f.params.map fun p => p.ty.toLean)
        ++ s!" → {retRepr}"
      s!"def {f.name} : {tyStr}\n\
         {"\n".intercalate armStrs}"
    else
      let paramNames := ", ".intercalate
        (f.params.map (·.name))
      s!"def {f.name} {paramBinds} {precBinds} \
         : {retRepr} :=\n\
         match {paramNames} with\n\
         {"\n".intercalate armStrs}"
  | .doBlock stmts ret =>
    let stmtStrs := stmts.map BodyStmt.toLean
    let retStr := s!"  {ret.toLeanWith
      f.name precondNames}"
    let allLines := stmtStrs ++ [retStr]
    let allBinds :=
      if precBinds.isEmpty then paramBinds
      else s!"{paramBinds} {precBinds}"
    if f.preconditions.isEmpty then
      s!"def {f.name} {allBinds} : {retRepr} := do\n\
         {"\n".intercalate allLines}"
    else
      s!"def {f.name} {allBinds} : {retRepr} := by\n\
         exact do\n\
         {"\n".intercalate allLines}\n\
         <;> sorry"
  | .expr body =>
    let rhsStr := body.toLeanWith f.name precondNames
    s!"def {f.name} {paramBinds} {precBinds} \
       : {retRepr} :=\n  {rhsStr}"

end FnDef

namespace PropertyDef

/-- Render a property definition to Lean syntax. -/
def toLean (p : PropertyDef) : String :=
  p.fnDef.toLean (isProperty := true)

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
  | .mkStruct _ args => args.flatMap calledNames
  | .index l i => l.calledNames ++ i.calledNames
  | .indexBang l i => l.calledNames ++ i.calledNames
  | .field e _ => e.calledNames
  | _ => []

end BodyExpr

namespace FnBody

/-- Collect all function/method names called. -/
def calledNames : FnBody → List String
  | .matchArms arms =>
    arms.flatMap fun a => a.rhs.calledNames
  | .doBlock stmts ret =>
    (stmts.flatMap fun
      | .let_ _ v => v.calledNames
      | .letBind _ v => v.calledNames)
    ++ ret.calledNames
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
