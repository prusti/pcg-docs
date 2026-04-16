import Lean

/-!
# `derive_base_functor`

A command macro that, given a simple recursive inductive type `T`, generates
the machinery for recursion schemes:

* `TF α` — the base (pattern) functor of `T`, a parallel inductive whose
  recursive positions are replaced by the type parameter `α`.
* `TF.fmap`, `TF.fmapM`, `instance : Functor TF`.
* `T.project : T → TF T`, `TF.embed : TF T → T` — the isomorphism
  witnessing that `T` is the fixed point of `TF`.
* `T.cata`, `T.cataM` — catamorphisms (standard and monadic).
* `T.para`, `T.paraM` — paramorphisms, which give the algebra access to the
  original subterm alongside the recursive result.

### Supported input shapes

The macro analyses every constructor argument type and understands the
following shape grammar w.r.t. the self-reference `T`:

```
Shape ::= noSelf | direct | List Shape | (β × Shape) | (Shape × β)
```

`direct` means the argument is `T` itself; `noSelf` means `T` does not
appear. Any other occurrence of `T` raises an error at elaboration time.
For multiple recursive types or deeper nestings, extend `Shape` and the two
lift renderers below.

### Usage

```
derive_base_functor DslExpr
```

places `DslExprF`, `DslExpr.project`, `DslExprF.embed`, `DslExpr.cata`,
`DslExpr.cataM`, `DslExpr.para`, `DslExpr.paraM` in the current namespace.

### Scope

Only single, non-indexed, non-mutual inductives without type parameters are
supported in v1. The macro errors out for anything else.
-/

namespace Meta.BaseFunctor

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- Shape of a constructor argument w.r.t. the self-reference. -/
inductive Shape
  | noSelf
  | direct
  | list (inner : Shape)
  | prodR (inner : Shape)
  | prodL (inner : Shape)
  deriving Inhabited

/-- True iff the constant `tName` appears anywhere in `e`. -/
private def containsSelf (tName : Name) (e : Expr) : Bool :=
  (e.find? fun sub => sub.isConstOf tName).isSome

/-- Analyse an argument type w.r.t. the self-reference `tName`. -/
private partial def analyse (tName : Name) (e : Expr) : MetaM Shape := do
  let e := e.consumeMData
  if e.isConstOf tName then
    return .direct
  if !containsSelf tName e then
    return .noSelf
  match e.getAppFnArgs with
  | (``List, #[a]) =>
    return .list (← analyse tName a)
  | (``Prod, #[l, r]) =>
    let sL ← analyse tName l
    let sR ← analyse tName r
    match sL, sR with
    | .noSelf, _ => return .prodR sR
    | _, .noSelf => return .prodL sL
    | _, _ =>
      throwError m!"derive_base_functor: unsupported type shape — both components of a Prod contain {tName}: {e}"
  | _ =>
    throwError m!"derive_base_functor: unsupported type shape containing {tName}: {e}"

/-- Render a pure lift: given source expression string `x : τ(α)` and a
    function `f : α → β`, produce a string for `τ(β)`. -/
private partial def renderLift (f x : String) (depth : Nat) : Shape → String
  | .noSelf => x
  | .direct => s!"({f} {x})"
  | .list s =>
    let y := s!"y{depth}"
    s!"(({x}).map (fun {y} => {renderLift f y (depth + 1) s}))"
  | .prodR s =>
    let y := s!"y{depth}"
    let a := s!"a{depth}"
    s!"(match {x} with | ({a}, {y}) => ({a}, {renderLift f y (depth + 1) s}))"
  | .prodL s =>
    let y := s!"y{depth}"
    let a := s!"a{depth}"
    s!"(match {x} with | ({y}, {a}) => ({renderLift f y (depth + 1) s}, {a}))"

/-- Render a monadic lift: produces `m τ(β)` from `τ(α)` under `f : α → m β`. -/
private partial def renderLiftM (f x : String) (depth : Nat) : Shape → String
  | .noSelf => s!"(pure {x})"
  | .direct => s!"({f} {x})"
  | .list s =>
    let y := s!"y{depth}"
    s!"(({x}).mapM (fun {y} => {renderLiftM f y (depth + 1) s}))"
  | .prodR s =>
    let y := s!"y{depth}"
    let a := s!"a{depth}"
    let inner := renderLiftM f y (depth + 1) s
    s!"((do let ({a}, {y}) := {x}; return ({a}, ← {inner})))"
  | .prodL s =>
    let y := s!"y{depth}"
    let a := s!"a{depth}"
    let inner := renderLiftM f y (depth + 1) s
    s!"((do let ({y}, {a}) := {x}; return (← {inner}, {a})))"

/-- Per-constructor analysis result: short name + list of (arg name, shape,
    type source as a string). -/
structure CtorInfo where
  short : String
  args  : List (String × Shape × String)

/-- Delaborate an `Expr` type to its Lean source form with `tName` replaced
    by the token `α`. -/
private def typeToSource (tName : Name) (αIdent : String) (e : Expr) :
    MetaM String := do
  let replaced := e.replace fun sub =>
    if sub.isConstOf tName then
      some (Expr.const (Name.mkSimple αIdent) [])
    else none
  let stx ← Lean.PrettyPrinter.delab replaced
  let fmt ← Lean.PrettyPrinter.ppTerm stx
  return fmt.pretty.trimAscii.toString

/-- Gather per-constructor data for generation. -/
private def gatherCtors (tName : Name) (iv : InductiveVal) :
    MetaM (List CtorInfo) := do
  iv.ctors.mapM fun ctorName => do
    let cInfo ← getConstInfoCtor ctorName
    forallTelescopeReducing cInfo.type fun xs _ => do
      let fields := xs.extract iv.numParams xs.size
      let mut args : List (String × Shape × String) := []
      for x in fields do
        let d ← x.fvarId!.getDecl
        let shape ← analyse tName d.type
        let typeSrc ← typeToSource tName "α" d.type
        args := args ++ [(d.userName.toString, shape, typeSrc)]
      let short := ctorName.replacePrefix tName Name.anonymous |>.toString
      return { short, args }

private def joinLines (ls : List String) : String :=
  String.intercalate "\n" ls

/-- Emit the `inductive TF (α : Type) where ...` block. -/
private def emitInductive (fName : String) (ctors : List CtorInfo) : String :=
  let ctorLine (c : CtorInfo) : String :=
    let argsPart := String.join (c.args.map fun (n, _, ty) => s!" ({n} : {ty})")
    s!"  | {c.short}{argsPart}"
  let header := s!"inductive {fName} (α : Type) : Type where"
  let body := joinLines (ctors.map ctorLine)
  s!"{header}\n{body}\n  deriving Inhabited"

/-- Emit `T.project : T → TF T`. -/
private def emitProject (tName : String) (fName : String)
    (ctors : List CtorInfo) : String :=
  let armOf (c : CtorInfo) : String :=
    let patArgs := String.join (c.args.map fun (n, _, _) => s!" {n}")
    let appArgs := patArgs
    s!"  | .{c.short}{patArgs} => .{c.short}{appArgs}"
  let arms := joinLines (ctors.map armOf)
  s!"def {tName}.project : {tName} → {fName} {tName}\n{arms}"

/-- Emit `TF.embed : TF T → T`. -/
private def emitEmbed (tName : String) (fName : String)
    (ctors : List CtorInfo) : String :=
  let armOf (c : CtorInfo) : String :=
    let patArgs := String.join (c.args.map fun (n, _, _) => s!" {n}")
    let appArgs := patArgs
    s!"  | .{c.short}{patArgs} => .{c.short}{appArgs}"
  let arms := joinLines (ctors.map armOf)
  s!"def {fName}.embed : {fName} {tName} → {tName}\n{arms}"

private def ob : String := "{"
private def cb : String := "}"

/-- Emit `TF.fmap : (α → β) → TF α → TF β`. -/
private def emitMap (fName : String) (ctors : List CtorInfo) : String :=
  let armOf (c : CtorInfo) : String :=
    let patArgs := String.join (c.args.map fun (n, _, _) => s!" {n}")
    let appArgs := String.join (c.args.map fun (n, s, _) =>
      match s with
      | .noSelf => s!" {n}"
      | _       => " " ++ renderLift "f" n 0 s)
    s!"  | .{c.short}{patArgs} => .{c.short}{appArgs}"
  let arms := joinLines (ctors.map armOf)
  let sig := "def " ++ fName ++ ".fmap " ++ ob ++ "α β : Type" ++ cb
    ++ " (f : α → β) : " ++ fName ++ " α → " ++ fName ++ " β"
  sig ++ "\n" ++ arms

/-- Emit `TF.fmapM [Monad m] (α → m β) → TF α → m (TF β)`. -/
private def emitMapM (fName : String) (ctors : List CtorInfo) : String :=
  let armOf (c : CtorInfo) : String :=
    let patArgs := String.join (c.args.map fun (n, _, _) => s!" {n}")
    -- Emit a `do` block: bind non-noSelf args via ←, pass noSelf args through.
    let binds : List String := c.args.filterMap fun (n, s, _) =>
      match s with
      | .noSelf => none
      | _       => some s!"      let {n}_ ← {renderLiftM "f" n 0 s}"
    let appArgs := String.join (c.args.map fun (n, s, _) =>
      match s with
      | .noSelf => s!" {n}"
      | _       => s!" {n}_")
    if binds.isEmpty then
      s!"  | .{c.short}{patArgs} => pure (.{c.short}{appArgs})"
    else
      let bindBlock := joinLines binds
      s!"  | .{c.short}{patArgs} => do\n{bindBlock}\n      return .{c.short}{appArgs}"
  let arms := joinLines (ctors.map armOf)
  let sig := "def " ++ fName ++ ".fmapM " ++ ob ++ "m : Type → Type" ++ cb
    ++ " [Monad m] " ++ ob ++ "α β : Type" ++ cb
    ++ " (f : α → m β) : " ++ fName ++ " α → m (" ++ fName ++ " β)"
  sig ++ "\n" ++ arms

/-- Emit the `Functor` instance. -/
private def emitFunctorInstance (fName : String) : String :=
  "instance : Functor " ++ fName ++ " where map := " ++ fName ++ ".fmap"

/-- Emit `T.cata`. -/
private def emitCata (tName fName : String) : String :=
  joinLines [
    "partial def " ++ tName ++ ".cata " ++ ob ++ "β : Type" ++ cb
      ++ " [Inhabited β] (alg : " ++ fName ++ " β → β) : "
      ++ tName ++ " → β :=",
    "  fun e => alg (" ++ fName ++ ".fmap (" ++ tName
      ++ ".cata alg) (" ++ tName ++ ".project e))"
  ]

/-- Emit `T.cataM`. -/
private def emitCataM (tName fName : String) : String :=
  joinLines [
    "partial def " ++ tName ++ ".cataM " ++ ob ++ "m : Type → Type" ++ cb
      ++ " [Monad m] " ++ ob ++ "β : Type" ++ cb ++ " [Inhabited (m β)]",
    "    (alg : " ++ fName ++ " β → m β) : " ++ tName ++ " → m β :=",
    "  fun e => do",
    "    let mapped ← " ++ fName ++ ".fmapM (" ++ tName
      ++ ".cataM alg) (" ++ tName ++ ".project e)",
    "    alg mapped"
  ]

/-- Emit `T.para`. -/
private def emitPara (tName fName : String) : String :=
  joinLines [
    "partial def " ++ tName ++ ".para " ++ ob ++ "β : Type" ++ cb ++ " [Inhabited β]",
    "    (alg : " ++ fName ++ " (" ++ tName ++ " × β) → β) : "
      ++ tName ++ " → β :=",
    "  fun e => alg (" ++ fName ++ ".fmap (fun sub => (sub, "
      ++ tName ++ ".para alg sub)) (" ++ tName ++ ".project e))"
  ]

/-- Emit `T.paraM`. -/
private def emitParaM (tName fName : String) : String :=
  joinLines [
    "partial def " ++ tName ++ ".paraM " ++ ob ++ "m : Type → Type" ++ cb
      ++ " [Monad m] " ++ ob ++ "β : Type" ++ cb ++ " [Inhabited (m β)]",
    "    (alg : " ++ fName ++ " (" ++ tName ++ " × β) → m β) : "
      ++ tName ++ " → m β :=",
    "  fun e => do",
    "    let mapped ← " ++ fName
      ++ ".fmapM (fun sub => do return (sub, ← " ++ tName
      ++ ".paraM alg sub)) (" ++ tName ++ ".project e)",
    "    alg mapped"
  ]

/-- Parse and elaborate a generated command source (exactly one command). -/
private def elabSource (src : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error msg =>
    throwError m!"derive_base_functor: failed to parse generated source.\nError: {msg}\nSource:\n{src}"
  | .ok stx =>
    elabCommand stx

/-- `derive_base_functor T` — see module docs. -/
syntax (name := deriveBaseFunctor)
  "derive_base_functor " ident : command

@[command_elab deriveBaseFunctor]
def elabDeriveBaseFunctor : CommandElab := fun stx => do
  let tIdent : Ident := ⟨stx[1]⟩
  let env ← getEnv
  -- Resolve the ident to a global const name, falling back to the raw id.
  let tName : Name :=
    match env.find? tIdent.getId with
    | some _ => tIdent.getId
    | none =>
      match env.find? (`_root_ ++ tIdent.getId) with
      | some _ => `_root_ ++ tIdent.getId
      | none => tIdent.getId
  let some (.inductInfo iv) := env.find? tName
    | throwError m!"derive_base_functor: {tName} is not an inductive type"
  unless iv.numIndices == 0 do
    throwError m!"derive_base_functor: indexed inductive {tName} is not supported"
  unless iv.all.length == 1 do
    throwError m!"derive_base_functor: mutual inductive {tName} is not supported"
  unless iv.numParams == 0 do
    throwError m!"derive_base_functor: parameterised inductive {tName} is not supported"

  let ctors ← liftTermElabM <| gatherCtors tName iv
  let tShort := tName.toString
  let fShort := tShort ++ "F"

  for src in [
    emitInductive fShort ctors,
    emitProject tShort fShort ctors,
    emitEmbed tShort fShort ctors,
    emitMap fShort ctors,
    emitMapM fShort ctors,
    emitFunctorInstance fShort,
    emitCata tShort fShort,
    emitCataM tShort fShort,
    emitPara tShort fShort,
    emitParaM tShort fShort
  ] do
    elabSource src

end Meta.BaseFunctor
