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
    lowered to `LeanExpr`. `selfName` and `proofArgs` drive insertion of
    precondition proof arguments at recursive calls; `calleeProofNames`
    lists callees requiring `sorry` arguments. `proofArgs` is the precomputed
    list of precondition proof terms (rendered as `raw` to bypass the
    atomic-arg re-parenthesisation logic in `LeanExpr.toAtom`).

    `withProofMarkers` wraps each `.leanProof t` rendering in a
    `Core.Dsl.IdentRefs.dslProofMarker (t)` placeholder so the
    in-tree DSL elaborator can graft the user's original
    `proof[…]` body syntax over the parsed-from-string copy
    after the surrounding declaration has been parsed. The
    export pipeline leaves this off (default) so generated
    `.lean` files contain the proof terms verbatim. -/
private def toLeanASTAlg
    (selfName : String)
    (calleeProofNames : List String) (proofArgs : List LeanExpr)
    (withProofMarkers : Bool) :
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
    if fnName == selfName && !proofArgs.isEmpty then
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
  | .forall_ binders b => .forall_ binders b
  | .sorryProof => .raw "sorry"
  | .leanProof t =>
    if withProofMarkers then
      .raw s!"(Core.Dsl.IdentRefs.dslProofMarker ({t}))"
    else .raw t
  | .match_ scrut arms eqName =>
    .match_ scrut (arms.map fun (pats, rhs) =>
      .mk (pats.map BodyPat.toLeanAST) rhs) eqName
  | .letIn pat val body => .letIn pat.toLeanAST val body
  | .letBindIn pat val body =>
    .letBindIn pat.toLeanAST val body
  | .ifThenElse c t e => .ifThenElse c t e
  | .neq l r => .binop "≠" l r
  | .eq l r => .binop "==" l r
  | .propEq l r => .binop "=" l r
  | .memberOf l r => .binop "∈" l r
  | .anyList list param body =>
    -- `list.any (fun param => body)` in Lean.
    .dot list "any" [.lambda param body]
  | .structUpdate recv fieldName value =>
    .recordUpdate recv fieldName value
  -- Formatting hints are presentation-only; the Lean export
  -- transparently passes the recursively-lowered body through.
  | .formatHint _ body => body

/-- Lower a `DslExpr` to a `LeanExpr`.
    `selfName` is the current function name (for
    inserting proof arguments at recursive calls).
    `precondProofs` lists the proof-term strings (one per
    precondition, in order) to splice as additional
    arguments at recursive call sites. Typically each entry
    is a `(by simp_all [name])` for a named precondition or
    `(by simp_all)` for a general expression precondition.
    `calleeProofNames` lists callee functions that also
    require `sorry` arguments. -/
def toLeanASTWith
    (selfName : String)
    (precondProofs : List String)
    (calleeProofNames : List String := [])
    (withProofMarkers : Bool := false)
    (e : DslExpr) : LeanExpr :=
  let proofArgs : List LeanExpr :=
    precondProofs.map (LeanExpr.raw)
  DslExpr.cata
    (toLeanASTAlg selfName calleeProofNames proofArgs
      withProofMarkers) e

partial def toLeanAST (e : DslExpr) : LeanExpr :=
  e.toLeanASTWith "" []

partial def toLeanWith
    (selfName : String)
    (precondProofs : List String)
    (calleeProofNames : List String := [])
    (withProofMarkers : Bool := false)
    (e : DslExpr) : String :=
  toString (e.toLeanASTWith selfName precondProofs
    calleeProofNames withProofMarkers)

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

/-- Lower an enum definition to an `inductive` declaration.
    `mapSetTypes` names struct types that transitively hold a
    `Map`/`Set`; any constructor whose argument references one
    such type is flagged via `LeanCtor.usesMapSet` so the
    renderer can suppress `BEq`/`Hashable`/`Inhabited`
    derives. -/
def toLeanASTWith (e : EnumDef)
    (mapSetTypes : List String) : LeanDecl :=
  .inductive_ e.name.name e.typeParams <|
    e.variants.map fun v =>
      let argUsesMapSet := v.args.any fun a =>
        a.type.usesMap || a.type.usesSet ||
        a.type.namedTypes.any (mapSetTypes.contains ·)
      { name := v.name.name
        args := v.args.map fun a =>
          { name := a.name, type := a.type.toLeanAST }
        usesMapSet := argUsesMapSet }

/-- Lower an enum definition to a `LeanDecl`. -/
def toLeanAST (e : EnumDef) : LeanDecl :=
  e.toLeanASTWith []

/-- Render an enum definition to a Lean `inductive`. -/
def toLean (e : EnumDef) : String :=
  toString e.toLeanAST

end EnumDef

-- ══════════════════════════════════════════════
-- FnDef / PropertyDef → LeanDecl
-- ══════════════════════════════════════════════

/-- Build precondition binders for a generated def. A named
    `prop(a, b)` becomes `(h_prop : prop a b)`; an
    expression-form precondition becomes `(h_pre<i> : <expr>)`
    where `i` is the precondition's positional index. -/
private def precondBinders
    (preconds : List Precondition) : List LeanBinder :=
  preconds.zipIdx.map fun (pc, i) => match pc with
    | .named n args =>
      let argStr := " ".intercalate args
      { name := s!"h_{n}"
        type := .const s!"{n} {argStr}" }
    | .expr_ e =>
      { name := s!"h_pre{i}"
        type := .const e.toLean }

/-- Render a precondition as a Lean source-level expression
    suitable for splicing into a recursive-call proof obligation
    or any other context where we need its propositional form
    (`prop a b` or the rendered DslExpr). -/
private def precondLean : Precondition → String
  | .named n args =>
    if args.isEmpty then n
    else s!"{n} {" ".intercalate args}"
  | .expr_ e => e.toLean

/-- The Lean proof-tactic string spliced as the proof argument
    of a self-recursive call. Tries `assumption` first (so a
    recursive call that passes the same argument as the
    enclosing function inherits its named hypothesis directly
    without forcing simp to unfold the property), and falls
    back to `simp_all [name]` for named preconditions or plain
    `simp_all` for expression-form preconditions. -/
private def precondProof : Precondition → String
  | .named n _ =>
    s!"(by first | assumption | simp_all [{n}])"
  | .expr_ _ => "(by first | assumption | simp_all)"

/-- Render a postcondition as a Lean source-level expression
    used inside the subtype return wrapper. -/
private def postcondLean : Postcondition → String
  | .named n args =>
    if args.isEmpty then n
    else s!"{n} {" ".intercalate args}"
  | .expr_ e => e.toLean

/-- Build the conjunction of postcondition applications used
    inside the subtype return wrapper. The literal argument
    name `result` (in the named form) refers to the function's
    return value. -/
private def postcondPredicate
    (postconds : List Postcondition) : String :=
  " ∧ ".intercalate (postconds.map postcondLean)

/-- Wrap a `LeanTy` return type in the postcondition subtype
    `\{ result : RetTy // P₁ ∧ P₂ ∧ … }` when postconds are
    present; otherwise return the original type. -/
private def wrapRetType
    (retTy : LeanTy)
    (postconds : List Postcondition) : LeanTy :=
  if postconds.isEmpty then retTy
  else .const
    s!"\{ result : {retTy.toString} // \
       {postcondPredicate postconds} }"

/-- Wrap a `LeanExpr` body with the subtype anonymous
    constructor `⟨body, <proof>⟩` when postconds are present;
    otherwise return the body unchanged. The proof tactic
    starts with `decide` so postconds that hold by computation
    on the literal body discharge cleanly (no `sorry` warning),
    falling back to `sorry` when `decide` doesn't apply. -/
private def wrapBodyExpr
    (body : LeanExpr)
    (postconds : List Postcondition) : LeanExpr :=
  if postconds.isEmpty then body
  else .anonCtor [body, .raw "by first | trivial | decide | sorry"]

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
  let precondProofs := f.preconditions.map precondProof
  let baseRetType : LeanTy :=
    if isProperty then .const "Prop"
    else f.returnType.toLeanAST
  let retType := wrapRetType baseRetType f.postconditions
  let params := paramBinders f.params
  let precBinds := precondBinders f.preconditions
  let wrap : LeanExpr → LeanExpr := fun e =>
    wrapBodyExpr e f.postconditions
  let body : LeanFnBody :=
    match f.body with
    | .matchArms arms =>
      let armASTs : List LeanMatchArm := arms.map fun arm =>
        .mk (arm.pat.map BodyPat.toLeanAST)
            (wrap (arm.rhs.toLeanASTWith f.name precondProofs))
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
      .expr (wrap (body.toLeanASTWith f.name precondProofs))
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

namespace DslExpr

/-- Flatten a right-associated `And` chain into the list of
    its conjuncts. `A ∧ B ∧ C` becomes `[A, B, C]`; a non-`And`
    expression becomes a singleton list. -/
private partial def flattenAnd : DslExpr → List DslExpr
  | .and l r => l :: flattenAnd r
  | e => [e]

/-- Extract a name suggestion from the head of `e` — the
    callee of a function-call expression or the identifier
    itself. Peels off `formatHint` wrappers (the `‹break›`
    hint, etc.) so a hinted antecedent still surfaces its
    underlying head. Returns `none` for shapes
    (like `=`/`≠`/literals) where no obvious "head" exists. -/
private partial def headIdent? : DslExpr → Option String
  | .call (.var n) _ => some n
  | .var n => some n
  | .formatHint _ body => headIdent? body
  | _ => none

/-- Pick a fresh `h_<head>` binder name for the i-th conjunct,
    falling back to `h_pre<i>` if the head can't be extracted
    and to `h_<head><i>` to disambiguate from earlier names. -/
private def conjunctBinderName
    (used : List String) (e : DslExpr) (i : Nat) : String :=
  let base := match headIdent? e with
    | some n => s!"h_{n}"
    | none => s!"h_pre{i}"
  if used.contains base then s!"{base}{i}" else base

/-- Flatten a right-associated `→` chain into the list of
    antecedents and the final goal. `A → B → C → G` becomes
    `([A, B, C], G)`; a non-`→` expression yields `([], e)`. -/
private partial def flattenImplies
    : DslExpr → List DslExpr × DslExpr
  | .implies l r =>
    let (rest, goal) := flattenImplies r
    (l :: rest, goal)
  | e => ([], e)

/-- Whether `e` (or any subterm) contains a `proof[h_…]`
    reference, indicating the user expects the surrounding
    property body to introduce named-Pi hypotheses (`h_<head>`
    binders) that the reference resolves against. Used by
    `bindAntecedentNames` to decide whether a bare ∧-chain
    should curry into Pi-binders or stay as a pure conjunction
    (e.g. `validPlace`'s `_ < _ ∧ validProjTy …`, where
    callers project via `h_validPlace.2` and currying would
    silently break them). -/
private partial def hasHypothesisRef : DslExpr → Bool
  | .leanProof t => t.startsWith "h_"
  | .var _ | .natLit _ | .true_ | .false_ | .emptyList
  | .none_ | .emptySet | .sorryProof => false
  | .some_ x | .dot x _ | .field x _ | .setSingleton x
  | .forall_ _ x | .lambda _ x => hasHypothesisRef x
  | .cons l r | .append l r | .flatMap l r | .map l r
  | .index l r | .indexBang l r | .lt l r | .le l r
  | .add l r | .sub l r | .mul l r | .div l r
  | .setUnion l r | .and l r | .or l r | .implies l r
  | .neq l r | .eq l r | .propEq l r | .memberOf l r =>
    hasHypothesisRef l || hasHypothesisRef r
  | .anyList l _ b | .setAll l _ b | .setFlatMap l _ b
  | .letIn _ l b | .letBindIn _ l b =>
    hasHypothesisRef l || hasHypothesisRef b
  | .ifThenElse c t f =>
    hasHypothesisRef c || hasHypothesisRef t || hasHypothesisRef f
  | .foldlM fn init list =>
    hasHypothesisRef fn || hasHypothesisRef init
      || hasHypothesisRef list
  | .mkStruct _ args => args.any hasHypothesisRef
  | .call fn args =>
    hasHypothesisRef fn || args.any hasHypothesisRef
  | .ineqChain _ es => es.any hasHypothesisRef
  | .match_ s arms _ =>
    hasHypothesisRef s || arms.any (hasHypothesisRef ·.2)
  | .structUpdate r _ v =>
    hasHypothesisRef r || hasHypothesisRef v
  | .formatHint _ b => hasHypothesisRef b

/-- Rewrite a property body's antecedent chain into a sequence of
    named-binder Pi binders so that earlier preconditions are in
    scope as `h_<head>` hypotheses for later antecedents and the
    goal. Two shapes are recognised:

    * `A₁ ∧ A₂ ∧ … ∧ Aₙ → G` — a single `→` whose antecedent is
      a `∧`-chain; each conjunct becomes a named Pi binder.
    * `A₁ → A₂ → … → Aₙ → G` — a pure `→`-chain; each
      antecedent becomes a named Pi binder. Single-implication
      bodies (`A → G`) are still rewritten so `A`'s head names
      a hypothesis the goal can reference.

    Each `hᵢ` is auto-named from `Aᵢ`'s head identifier (see
    `conjunctBinderName`); the antecedent's rendered Lean source
    becomes the binder's `typeName`, so a later occurrence of
    `proof[hᵢ]` in the goal or in a later antecedent
    resolves to a real hypothesis instead of `sorry`. The DSL
    `FnBody` registry entry is left untouched, so the LaTeX
    renderer continues to display the original `∧`/`→` shape.

    Walks through leading `forall_` binders so the rewrite
    reaches the eventual antecedent chain, and recursively
    descends into the goal so a `∧`-chain followed by a
    `→`-chain (or vice-versa) is fully named.

    `withProofMarkers` controls how each rewritten antecedent
    is stringified into its `forall_` binder type: when `true`,
    `proof[…]` bodies inside an antecedent are rendered with
    `dslProofMarker (…)` placeholders so the in-tree DSL
    elaborator's `graftDslProofMarkers` pass can splice the
    user-source syntax back in. The export pipeline calls this
    with the default `false` so generated `.lean` files stay
    free of marker calls. -/
partial def bindAntecedentNames
    (withProofMarkers : Bool := false) : DslExpr → DslExpr :=
  let antToString (ant : DslExpr) : String :=
    ant.toLeanWith "" [] [] withProofMarkers
  let nameAndBind (antecedents : List DslExpr) (goal : DslExpr)
      : DslExpr :=
    let assignNames :
        List String × List String → DslExpr × Nat →
        List String × List String :=
      fun (used, acc) (e, i) =>
        let name := conjunctBinderName used e i
        (name :: used, name :: acc)
    let (_, namesRev) :=
      antecedents.zipIdx.foldl assignNames ([], [])
    let names := namesRev.reverse
    -- Each antecedent becomes its own one-element binder group
    -- so the resulting Pi chain is rendered as a sequence of
    -- `(hᵢ : Aᵢ)` Lean binders.
    (names.zip antecedents).foldr
      (fun (name, ant) acc =>
        .forall_ [([name], some (antToString ant))] acc)
      goal
  fun e => match e with
  | .forall_ binders body =>
    .forall_ binders (bindAntecedentNames withProofMarkers body)
  | .implies (.and l r) goal =>
    let antecedents := flattenAnd (.and l r)
    nameAndBind antecedents
      (bindAntecedentNames withProofMarkers goal)
  | .implies _ _ =>
    let (antecedents, goal) := flattenImplies e
    if antecedents.isEmpty then e
    else nameAndBind antecedents
      (bindAntecedentNames withProofMarkers goal)
  -- Bare top-level `A₁ ∧ A₂ ∧ … ∧ Aₙ` (no enclosing `→`): when
  -- the body references some `proof[h_…]` between
  -- clauses, elect the rightmost conjunct as the implicit goal
  -- and the others as named-Pi antecedents. This lets a
  -- `defProperty` body written as a ∧-chain (e.g. `Framing'`,
  -- `NoAlias'`, `FramingInvariant'`) carry hypothesis
  -- references between clauses without an explicit `→ goal` at
  -- the end. ∧-chains that don't carry hypothesis references
  -- (e.g. `validPlace`'s `_ < _ ∧ validProjTy …`, where
  -- callers project via `h_validPlace.2`) keep their pure
  -- conjunction shape — currying them would break those
  -- projections.
  | .and l r =>
    if hasHypothesisRef e then
      let conjuncts := flattenAnd (.and l r)
      match conjuncts.dropLast, conjuncts.getLast? with
      | _, none => e
      | [], _ => e
      | antecedents, some goal =>
        nameAndBind antecedents
          (bindAntecedentNames withProofMarkers goal)
    else e
  | _ => e

end DslExpr

namespace PropertyDef

/-- Lower a property to a `LeanDecl`. The body is rewritten
    so that a top-level `A₁ ∧ … ∧ Aₙ → G` antecedent becomes
    a chain of named `(hᵢ : Aᵢ)` Pi binders — each
    precondition's proof is then in scope for any
    `proof[hᵢ]` reference inside `G` or in a later
    antecedent. The DSL `FnBody` registry entry is left
    untouched, so the LaTeX renderer continues to display
    the original conjunction-style implication. -/
def toLeanAST (p : PropertyDef) : LeanDecl :=
  let curriedBody : FnBody := match p.fnDef.body with
    | .expr e => .expr e.bindAntecedentNames
    | .matchArms arms => .matchArms (arms.map fun arm =>
        BodyArm.mk arm.pat arm.rhs.bindAntecedentNames)
  let curried := { p.fnDef with body := curriedBody }
  curried.toLeanAST (isProperty := true)

/-- Render a property definition to Lean syntax. -/
def toLean (p : PropertyDef) : String :=
  toString p.toLeanAST

end PropertyDef

namespace InductivePropertyDef

/-- All named types referenced by the parameters of an
    inductive property. The rule premises and conclusion are
    handled by `referencedNames` below (which depends on
    `DslExpr.calledNames`, defined later in this file). -/
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
  | .dot (_, recv) method => method :: recv
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
  | .match_ (_, scrut) arms _ =>
    scrut ++ arms.flatMap (fun (_, (_, rhs)) => rhs)
  | .letIn _ (_, v) (_, b) => v ++ b
  | .letBindIn _ (_, v) (_, b) => v ++ b
  | .ifThenElse (_, c) (_, t) (_, e) => c ++ t ++ e
  | .neq (_, l) (_, r) => l ++ r
  | .eq (_, l) (_, r) => l ++ r
  | .propEq (_, l) (_, r) => l ++ r
  | .memberOf (_, l) (_, r) => l ++ r
  | .anyList (_, l) _ (_, b) => l ++ b
  | .structUpdate (_, recv) _ (_, value) => recv ++ value
  | .formatHint _ (_, body) => body

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
    preconditions, postconditions, called functions). -/
def referencedNames (f : FnDef) : List String :=
  f.referencedTypes ++
  f.preconditions.flatMap precondCalledNames ++
  f.postconditions.flatMap postcondCalledNames ++
  f.body.calledNames
where
  precondCalledNames : Precondition → List String
    | .named n _ => [n]
    | .expr_ e => e.calledNames
  postcondCalledNames : Postcondition → List String
    | .named n _ => [n]
    | .expr_ e => e.calledNames

/-- Whether this function uses `Set` anywhere. -/
def usesSet (f : FnDef) : Bool :=
  f.returnType.usesSet ||
  f.params.any fun p => p.ty.usesSet

end FnDef

namespace InductivePropertyDef

/-- All names — types and called functions / variants — that
    this inductive property depends on, including those that
    appear in rule premises and conclusions. Used by the
    Lean-export topo sort so a property whose rules mention
    later-declared identifiers is still emitted after its
    dependencies. -/
def referencedNames (p : InductivePropertyDef) : List String :=
  p.referencedTypes ++
    p.rules.flatMap fun r =>
      r.conclusion.calledNames ++
      r.premises.flatMap (·.calledNames)

end InductivePropertyDef
