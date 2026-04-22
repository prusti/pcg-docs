/-- Operator in an inequality chain. -/
inductive IneqOp where
  /-- Strict less-than: `<`. -/
  | lt
  /-- Less-than-or-equal: `≤`. -/
  | le
  deriving Repr, Inhabited, BEq

/-!
# LeanAST

A structured representation of Lean syntax used as an
intermediate representation when generating Lean code.

DSL types in `Core.Dsl.*` are first lowered to values of
the AST defined here, and the resulting tree is then
rendered to a `String` via `toString`. Doing it this way
keeps string manipulation out of the export pipeline and
makes illegal Lean syntax much harder to construct.
-/

namespace LeanAST

-- ══════════════════════════════════════════════
-- Types
-- ══════════════════════════════════════════════

/-- A Lean type expression. -/
inductive LeanTy where
  /-- Atomic type identifier (e.g. `Nat`, `Foo`). -/
  | const (name : String)
  /-- Type application: `head arg`. The argument is
      always parenthesized when rendered. -/
  | app (head : String) (arg : LeanTy)
  /-- Two-argument type application: `head arg1 arg2`. -/
  | app2 (head : String) (arg1 : LeanTy) (arg2 : LeanTy)
  /-- N-argument type application: `head arg1 arg2 …`.
      Each argument is parenthesized when rendered. -/
  | appN (head : String) (args : List LeanTy)
  /-- Function arrow: `from → to`. -/
  | arrow (from_ : LeanTy) (to_ : LeanTy)
  /-- Cartesian product: `a × b × …`. -/
  | product (parts : List LeanTy)
  deriving Inhabited

mutual

partial def LeanTy.toString : LeanTy → String
  | .const n => n
  | .app head arg => s!"{head} ({arg.toString})"
  | .app2 head a b =>
    s!"{head} ({a.toString}) ({b.toString})"
  | .appN head args =>
    let argStrs := args.map fun a => s!"({a.toString})"
    s!"{head} {" ".intercalate argStrs}"
  | .arrow a b => s!"{a.toString} → {b.toString}"
  | .product ts => " × ".intercalate (ts.map LeanTy.toString)

end

instance : ToString LeanTy := ⟨LeanTy.toString⟩

-- ══════════════════════════════════════════════
-- Patterns
-- ══════════════════════════════════════════════

/-- A pattern in a `match` arm. -/
inductive LeanPat where
  | wild
  | var (name : String)
  /-- Constructor pattern `.name args…`. -/
  | ctor (name : String) (args : List LeanPat)
  /-- Anonymous constructor pattern `⟨a, b, …⟩`. -/
  | anonCtor (args : List LeanPat)
  /-- Empty list pattern `[]`. -/
  | listNil
  /-- Cons pattern `h :: t`. -/
  | listCons (head : LeanPat) (tail : LeanPat)
  /-- Numeric literal pattern. -/
  | natLit (n : Nat)
  deriving Inhabited

partial def LeanPat.toString : LeanPat → String
  | .wild => "_"
  | .var n => n
  | .anonCtor args =>
    s!"⟨{", ".intercalate (args.map LeanPat.toString)}⟩"
  | .ctor n args =>
    let prefix_ := if n.contains '.' then "" else "."
    if args.isEmpty then s!"{prefix_}{n}"
    else
      let argStr := " ".intercalate
        (args.map fun a => match a with
          | .wild => "_"
          | .var v => v
          | _ => s!"({a.toString})")
      s!"{prefix_}{n} {argStr}"
  | .listNil => "[]"
  | .listCons h t =>
    let hStr := match h with
      | .ctor _ (_ :: _) => s!"({h.toString})"
      | _ => h.toString
    s!"{hStr} :: {t.toString}"
  | .natLit n => ToString.toString n

instance : ToString LeanPat := ⟨LeanPat.toString⟩

-- ══════════════════════════════════════════════
-- Expressions
-- ══════════════════════════════════════════════

mutual

/-- A Lean term. -/
inductive LeanExpr where
  | ident (name : String)
  | natLit (n : Nat)
  /-- Boolean literal. -/
  | boolLit (b : Bool)
  /-- `none`. -/
  | noneE
  /-- `some e`. -/
  | someE (e : LeanExpr)
  /-- Empty list literal `[]`. -/
  | listNil
  /-- Cons `h :: t`. -/
  | listCons (head : LeanExpr) (tail : LeanExpr)
  /-- List append `l ++ r`. -/
  | listAppend (l : LeanExpr) (r : LeanExpr)
  /-- Empty set `(∅ : Set _)`. -/
  | emptySet
  /-- Anonymous constructor `⟨a, b, …⟩`. -/
  | anonCtor (args : List LeanExpr)
  /-- Method call `recv.method args…`. -/
  | dot (recv : LeanExpr) (method : String)
        (args : List LeanExpr)
  /-- Field projection `recv.name`. -/
  | field (recv : LeanExpr) (name : String)
  /-- Indexing `list[idx]?`. -/
  | index (list : LeanExpr) (idx : LeanExpr)
  /-- Indexing `list[idx]!`. -/
  | indexBang (list : LeanExpr) (idx : LeanExpr)
  /-- Prefix function call `fn arg₁ arg₂ …`. The
      arguments are wrapped in parens individually
      when rendered if they aren't atomic. -/
  | app (fn : String) (args : List LeanExpr)
  /-- Binary operator: `lhs OP rhs`. The op is the raw
      Lean operator string, e.g. `"<"`, `"+"`, `"∧"`. -/
  | binop (op : String) (lhs : LeanExpr) (rhs : LeanExpr)
  /-- Chained inequality: `a < b ∧ b ≤ c ∧ …`.
      Each `IneqOp` in `ops` connects successive
      expressions; `ops.length = es.length - 1`. -/
  | ineqChain (ops : List IneqOp) (es : List LeanExpr)
  /-- Bounded `∀ x ∈ s, body`. -/
  | forallIn (binder : String) (set : LeanExpr)
             (body : LeanExpr)
  /-- Plain `∀ x, body`. -/
  | forall_ (binder : String) (body : LeanExpr)
  /-- `match scrut with | … => …`. -/
  | match_ (scrut : LeanExpr) (arms : List LeanMatchArm)
  /-- `let n := v\nbody`. -/
  | letIn (name : String) (val : LeanExpr)
          (body : LeanExpr)
  /-- `do let n ← v; body` (Option monad bind). -/
  | letBindIn (name : String) (val : LeanExpr)
              (body : LeanExpr)
  /-- `if c then t else e`. -/
  | ifThenElse (cond : LeanExpr) (then_ : LeanExpr)
               (else_ : LeanExpr)
  /-- `list.flatMap fun param => body`. -/
  | listFlatMap (list : LeanExpr) (param : String)
                (body : LeanExpr)
  /-- `list.map fun param => body`. -/
  | listMap (list : LeanExpr) (param : String)
            (body : LeanExpr)
  /-- `list.map fn`. -/
  | listMapFn (list : LeanExpr) (fn : String)
  /-- `Set.flatMapList list fun param => body`. -/
  | setFlatMapList (list : LeanExpr) (param : String)
                   (body : LeanExpr)
  /-- `list.foldlM fn init`. -/
  | foldlM (list : LeanExpr) (fn : String)
           (init : LeanExpr)
  /-- Lambda: `fun param => body`. -/
  | lambda (param : String) (body : LeanExpr)
  /-- A raw escape hatch (used for `sorry` and
      hand-written proof terms). The contents are
      copied verbatim. -/
  | raw (text : String)
  deriving Inhabited

/-- A `match` arm. -/
inductive LeanMatchArm where
  | mk (pats : List LeanPat) (rhs : LeanExpr)

end

deriving instance Inhabited for LeanExpr
deriving instance Inhabited for LeanMatchArm

mutual

/-- Render an expression. -/
partial def LeanExpr.toString : LeanExpr → String
  | .ident n => n
  | .natLit n => ToString.toString n
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .noneE => "none"
  | .someE e => s!"some {e.toAtom}"
  | .listNil => "[]"
  | .listCons h t =>
    s!"{h.toString} :: {t.toString}"
  | .listAppend l r =>
    s!"{l.toString} ++ {r.toString}"
  | .emptySet => "(∅ : Set _)"
  | .anonCtor args =>
    s!"⟨{", ".intercalate (args.map LeanExpr.toString)}⟩"
  | .dot recv "toSet" [] =>
    s!"{recv.toAtom}.toSet"
  | .dot recv method [] =>
    s!"{recv.toAtom}.{method}"
  | .dot recv method args =>
    let argStr := " ".intercalate (args.map LeanExpr.toAtom)
    s!"{recv.toAtom}.{method} {argStr}"
  | .field recv name =>
    match recv with
    | .app _ _ => s!"({recv.toString}).{name}"
    | _ => s!"{recv.toString}.{name}"
  | .index l i =>
    s!"{l.toString}[{i.toString}]?"
  | .indexBang l i =>
    s!"{l.toString}[{i.toString}]!"
  | .app fn [] => fn
  | .app fn args =>
    let argStr := " ".intercalate (args.map LeanExpr.toAtom)
    s!"{fn} {argStr}"
  | .binop op l r =>
    let isArith := op == "+" || op == "-" || op == "/"
    let wrapIfNeeded (e : LeanExpr) :=
      match e with
      | .binop op' .. =>
        let childArith := op' == "+" || op' == "-"
            || op' == "/"
        if isArith && childArith
        then s!"({e.toString})" else e.toString
      | _ => e.toString
    s!"{wrapIfNeeded l} {op} {wrapIfNeeded r}"
  | .ineqChain ops es =>
    let opStr : IneqOp → String
      | .lt => "<" | .le => "≤"
    let pairs := ops.zip (es.zip (es.drop 1))
    " ∧ ".intercalate
      (pairs.map fun (op, l, r) =>
        s!"{l.toString} {opStr op} {r.toString}")
  | .forallIn binder set body =>
    s!"∀ {binder} ∈ {set.toString}, {body.toString}"
  | .forall_ binder body =>
    s!"∀ {binder}, {body.toString}"
  | .match_ scrut arms =>
    let armStrs := arms.map fun
      | .mk pats rhs =>
        let patStr := ", ".intercalate
          (pats.map LeanPat.toString)
        s!"  | {patStr} => {rhs.toString}"
    s!"(match {scrut.toString} with\n\
       {"\n".intercalate armStrs})"
  | .letIn name val body =>
    s!"let {name} := {val.toString}\n{body.toString}"
  | .letBindIn name val body =>
    s!"({val.toAtom}.bind (fun {name} => {body.toString}))"
  | .ifThenElse c t e =>
    s!"if {c.toString} then {t.toString} else {e.toString}"
  | .listFlatMap list param body =>
    s!"{list.toString}.flatMap fun {param} => \
       {body.toString}"
  | .listMap list param body =>
    s!"{list.toString}.map fun {param} => \
       {body.toString}"
  | .listMapFn list fn =>
    s!"{list.toString}.map {fn}"
  | .setFlatMapList list param body =>
    s!"Set.flatMapList {list.toAtom} fun {param} => \
       {body.toString}"
  | .foldlM list fn init =>
    s!"{list.toString}.foldlM {fn} {init.toString}"
  | .lambda param body =>
    s!"fun {param} => {body.toString}"
  | .raw t => t

/-- Render an expression in "argument" position,
    parenthesizing it if it isn't already atomic. -/
partial def LeanExpr.toAtom : LeanExpr → String
  | .ident n => n
  | .natLit n => ToString.toString n
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .noneE => "none"
  | .listNil => "[]"
  | .emptySet => "(∅ : Set _)"
  | e => s!"({e.toString})"

end

instance : ToString LeanExpr := ⟨LeanExpr.toString⟩

-- ══════════════════════════════════════════════
-- Declarations
-- ══════════════════════════════════════════════

/-- A `(name : type)` binder. -/
structure LeanBinder where
  name : String
  type : LeanTy
  deriving Inhabited

/-- A field of a `structure`. -/
structure LeanField where
  name : String
  type : LeanTy
  deriving Inhabited

/-- A constructor of an `inductive`. -/
structure LeanCtor where
  name : String
  args : List LeanBinder
  deriving Inhabited

/-- A do-block statement. -/
inductive LeanDoStmt where
  /-- `let name := val`. -/
  | letE (name : String) (val : LeanExpr)
  /-- `let name ← val`. -/
  | letBind (name : String) (val : LeanExpr)
  deriving Inhabited

/-- The body of a Lean function definition. -/
inductive LeanFnBody where
  /-- A pattern-matching function rendered as
      `def f : T₁ → T₂ → R\n  | ... => ...`
      when `paramTypes?` is given (and there are no
      precondition binders), or as
      `... := match params with ...` otherwise. -/
  | matchArms (arms : List LeanMatchArm)
  /-- A do-block body. -/
  | doBlock (stmts : List LeanDoStmt) (ret : LeanExpr)
  /-- A bare expression body. -/
  | expr (e : LeanExpr)
  deriving Inhabited

/-- A `def` declaration. -/
structure LeanDef where
  name : String
  /-- Function parameters. -/
  params : List LeanBinder
  /-- Precondition binders, rendered after the regular
      params. When non-empty, match-arm functions are
      rendered with an explicit `match … with` rather
      than the curried `def f : T → … → R\n  | …` form. -/
  precondBinds : List LeanBinder
  /-- Result type. -/
  retType : LeanTy
  body : LeanFnBody
  /-- If `true`, append `<;> sorry` after a do-block
      body wrapped in `by exact do …` (used by Property
      definitions to discharge precondition obligations). -/
  doRequiresProof : Bool := false
  deriving Inhabited

/-- A top-level Lean declaration. -/
inductive LeanDecl where
  | structure_ (name : String) (typeParams : List String)
      (fields : List LeanField)
  | inductive_ (name : String) (typeParams : List String)
      (ctors : List LeanCtor)
  | def_ (d : LeanDef)
  /-- A `abbrev Name (p1 : Type) ... := body` declaration. -/
  | abbrev_ (name : String) (typeParams : List String)
      (body : LeanTy)
  /-- Wrap a declaration in `namespace ns … end ns`. -/
  | namespaced (ns : String) (decl : LeanDecl)
  deriving Inhabited

-- ══════════════════════════════════════════════
-- Rendering of declarations
-- ══════════════════════════════════════════════

private def renderBinder (b : LeanBinder) : String :=
  s!"({b.name} : {b.type})"

private def renderField (f : LeanField) : String :=
  s!"  {f.name} : {f.type}"

private def renderCtor (c : LeanCtor) : String :=
  if c.args.isEmpty then s!"  | {c.name}"
  else
    let argStr := " ".intercalate
      (c.args.map renderBinder)
    s!"  | {c.name} {argStr}"

private def renderDoStmt : LeanDoStmt → String
  | .letE n v => s!"  let {n} := {v}"
  | .letBind n v => s!"  let {n} ← {v}"

private def renderMatchArms
    (arms : List LeanMatchArm) : List String :=
  arms.map fun
    | .mk pats rhs =>
      let patStr := ", ".intercalate
        (pats.map LeanPat.toString)
      s!"  | {patStr} => {rhs}"

private def renderDef (d : LeanDef) : String :=
  let paramBinds := " ".intercalate
    (d.params.map renderBinder)
  let precBinds := " ".intercalate
    (d.precondBinds.map renderBinder)
  let allBinds :=
    if d.precondBinds.isEmpty then paramBinds
    else s!"{paramBinds} {precBinds}"
  match d.body with
  | .matchArms arms =>
    let armStrs := renderMatchArms arms
    if d.precondBinds.isEmpty then
      let tyStr := " → ".intercalate
        ((d.params.map fun p => p.type.toString)
          ++ [d.retType.toString])
      s!"def {d.name} : {tyStr}\n\
         {"\n".intercalate armStrs}"
    else
      let paramNames := ", ".intercalate
        (d.params.map (·.name))
      s!"def {d.name} {allBinds} : {d.retType} :=\n\
         match {paramNames} with\n\
         {"\n".intercalate armStrs}"
  | .doBlock stmts ret =>
    let stmtStrs := stmts.map renderDoStmt
    let retStr := s!"  {ret}"
    let allLines := stmtStrs ++ [retStr]
    if d.doRequiresProof then
      s!"def {d.name} {allBinds} : {d.retType} := by\n\
         exact do\n\
         {"\n".intercalate allLines}\n\
         <;> sorry"
    else
      s!"def {d.name} {allBinds} : {d.retType} := do\n\
         {"\n".intercalate allLines}"
  | .expr body =>
    s!"def {d.name} {allBinds} : {d.retType} :=\n  {body}"

partial def LeanDecl.toString : LeanDecl → String
  | .structure_ name typeParams fields =>
    let fieldStrs := fields.map renderField
    let usesMap := fields.any fun f =>
      (f.type.toString).find? "HashMap" |>.isSome
    let usesSet := fields.any fun f =>
      let s := f.type.toString
      -- `HashSet T` from Runtime.Set; surface tokens match
      -- the `Set T`/`HashSet T` forms we may render.
      s.splitOn " " |>.any fun tok =>
        tok == "HashSet" || tok == "Set"
    let needsHashBounds := usesMap || usesSet
    -- Generic structs may hold fields whose types are generic
    -- inductives that don't derive `Inhabited` (e.g.
    -- `MaybeLabelledPlace P`), so omit `Inhabited` when the
    -- struct is itself generic. Matches the behaviour used
    -- for generic inductives below. Also skip `BEq`/`Hashable`
    -- when the struct stores a `HashMap`/`HashSet` — those
    -- underlying types don't derive `BEq`/`Hashable`, so the
    -- outer struct can't either.
    let derives := if usesMap || usesSet then
        if typeParams.isEmpty then "Repr, Inhabited" else "Repr"
      else
        if typeParams.isEmpty
          then "Repr, BEq, Hashable, Inhabited"
          else "Repr, BEq, Hashable"
    let tpStr :=
      if typeParams.isEmpty then ""
      else
        let binders := typeParams.map fun p =>
          if needsHashBounds then
            s!"({p} : Type) [BEq {p}] [Hashable {p}]"
          else
            s!"({p} : Type)"
        " " ++ " ".intercalate binders
    s!"structure {name}{tpStr} where\n\
       {"\n".intercalate fieldStrs}\n\
       deriving {derives}"
  | .inductive_ name typeParams ctors =>
    let ctorStrs := ctors.map renderCtor
    let tpStr :=
      if typeParams.isEmpty then ""
      else " " ++ " ".intercalate
        (typeParams.map fun p => s!"({p} : Type)")
    -- Generic inductives can't derive `Inhabited` without
    -- knowing the parameters are inhabited, so omit it.
    let derives := if typeParams.isEmpty
      then "Repr, BEq, Hashable, Inhabited"
      else "Repr, BEq, Hashable"
    s!"inductive {name}{tpStr} where\n\
       {"\n".intercalate ctorStrs}\n\
       deriving {derives}"
  | .def_ d => renderDef d
  | .abbrev_ name typeParams body =>
    let tpStr :=
      if typeParams.isEmpty then ""
      else " " ++ " ".intercalate
        (typeParams.map fun p => s!"({p} : Type)")
    s!"abbrev {name}{tpStr} := {body.toString}"
  | .namespaced ns inner =>
    s!"namespace {ns}\n\n{inner.toString}\n\nend {ns}"

instance : ToString LeanDecl := ⟨LeanDecl.toString⟩

-- ══════════════════════════════════════════════
-- Modules
-- ══════════════════════════════════════════════

/-- A complete Lean module: imports plus a list of
    top-level declarations rendered in order. -/
structure LeanModule where
  /-- Each entry is rendered as `import {name}`. -/
  imports : List String
  decls : List LeanDecl
  deriving Inhabited

def LeanModule.toString (m : LeanModule) : String :=
  let importLines := m.imports.map fun i => s!"import {i}"
  let header := if importLines.isEmpty then ""
    else "\n".intercalate importLines ++ "\n\n"
  let defs := m.decls.map LeanDecl.toString
  header ++ "\n\n".intercalate defs ++ "\n"

instance : ToString LeanModule := ⟨LeanModule.toString⟩

end LeanAST
