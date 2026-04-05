import Shared.RustSyntax
import Shared.EnumDef
import Shared.StructDef
import Shared.FnDef
import Shared.FType
import Shared.OrderDef
import Shared.Registry

/-- Capitalise the first character of a string. -/
def capitalise (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Indentation string for a given depth (4 spaces per level). -/
private def ind (n : Nat) : String :=
  String.ofList (List.replicate (n * 4) ' ')



namespace RustBinOp

/-- Render a binary operator. -/
def render : RustBinOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<"
  | .le => "<=" | .gt => ">" | .ge => ">="

end RustBinOp

namespace RustPat

/-- Render a pattern. -/
def render : RustPat → String
  | .ident n => n
  | .wild => "_"
  | .tuple ps =>
    let inner := ps.map RustPat.render
    s!"({String.intercalate ", " inner})"
  | .path p => p.render
  | .ref inner => s!"&{inner.render}"
  | .or pats =>
    String.intercalate " | " (pats.map RustPat.render)

end RustPat

namespace RustVis

/-- Render visibility prefix (empty or `pub `). -/
def render : RustVis → String
  | .priv => ""
  | .pub => "pub "

end RustVis

namespace RustAttr

/-- Render an attribute line. -/
def render : RustAttr → String
  | .derive traits =>
    s!"#[derive({String.intercalate ", " traits})]"
  | .other text => s!"#[{text}]"

end RustAttr

mutual
  /-- Render a Rust expression at the given indentation depth. -/
  partial def renderExpr (d : Nat) : RustExpr → String
    | .path p => p.render
    | .litStr s => s!"\"{s}\""
    | .litBool true => "true"
    | .litBool false => "false"
    | .call func args =>
      let argStrs := args.map (renderExpr d)
      s!"{renderExpr d func}({String.intercalate ", " argStrs})"
    | .unaryOp op e =>
      let opStr := match op with
        | .deref => "*" | .neg => "-" | .not => "!"
      s!"{opStr}{renderExpr d e}"
    | .binOp op lhs rhs =>
      s!"{renderExpr d lhs} {op.render} {renderExpr d rhs}"
    | .tuple elems =>
      let inner := elems.map (renderExpr d)
      s!"({String.intercalate ", " inner})"
    | .methodCall recv method args typeArgs =>
      let argStrs := args.map (renderExpr d)
      let turbo := if typeArgs.isEmpty then ""
        else s!"::<{String.intercalate ", "
          (typeArgs.map RustTy.render)}>"
      s!"{renderExpr d recv}.{method}{turbo}({String.intercalate ", " argStrs})"
    | .field recv name =>
      s!"{renderExpr d recv}.{name}"
    | .block stmts tail =>
      let i := ind (d + 1)
      let stmtStrs := stmts.map fun s =>
        s!"{i}{renderStmt (d + 1) s}"
      let tailStr := match tail with
        | some e => s!"{i}{renderExpr (d + 1) e}\n"
        | none => ""
      let body := String.intercalate "\n" stmtStrs
      let sep := if stmts.isEmpty then "" else "\n"
      s!"\{{sep}{body}{sep}{tailStr}{ind d}}"
    | .«if» cond then_ else_ =>
      let thenStr := renderExpr d then_
      match else_ with
      | none => s!"if {renderExpr d cond} {thenStr}"
      | some e =>
        s!"if {renderExpr d cond} {thenStr} else {renderExpr d e}"
    | .«match» scrutinee arms =>
      let i := ind (d + 1)
      let armStrs := arms.map fun a =>
        s!"{i}{renderMatchArm (d + 1) a}"
      let body := String.intercalate "\n" armStrs
      s!"match {renderExpr d scrutinee} \{\n\
         {body}\n{ind d}}"
    | .ref_ false e => s!"&{renderExpr d e}"
    | .ref_ true e => s!"&mut {renderExpr d e}"
    | .«return» none => "return"
    | .«return» (some e) => s!"return {renderExpr d e}"
    | .try_ e => s!"{renderExpr d e}?"
    | .closure params body =>
      let ps := String.intercalate ", " params
      s!"|{ps}| {renderExpr d body}"
    | .structInit path fields =>
      let i := ind (d + 1)
      let fieldStrs := fields.map fun (n, e) =>
        s!"{i}{n}: {renderExpr (d + 1) e},"
      s!"{path.render} \{\n\
         {String.intercalate "\n" fieldStrs}\n\
         {ind d}}"
    | .raw s => s

  /-- Render a match arm. -/
  partial def renderMatchArm : (d : Nat) → RustMatchArm → String
    | d, .mk pat body =>
      s!"{pat.render} => {renderExpr d body},"

  /-- Render a statement. -/
  partial def renderStmt : (d : Nat) → RustStmt → String
    | d, .expr e =>
      let semi := match e with
        | .«if» .. | .«match» .. => ""
        | _ => ";"
      s!"{renderExpr d e}{semi}"
    | d, .«let» pat ty val mutable =>
      let mutStr := if mutable then "mut " else ""
      let tyStr := match ty with
        | some t => s!": {t.render}"
        | none => ""
      s!"let {mutStr}{pat.render}{tyStr} = {renderExpr d val};"
end

namespace RustFn

/-- Render a function definition. -/
def render (d : Nat) (f : RustFn) : String :=
  let vis := f.vis.render
  let params := f.params.map fun p => match p with
    | .selfRef => "&self"
    | .selfMut => "&mut self"
    | .named pat ty => s!"{pat.render}: {ty.render}"
  let paramStr := String.intercalate ", " params
  let retStr := match f.retTy with
    | some t => s!" -> {t.render}"
    | none => ""
  let bodyStr := renderExpr d f.body
  s!"{vis}fn {f.name}({paramStr}){retStr} {bodyStr}"

end RustFn

/-- Generate `From<Box<T>>` impl items for types that
    might appear boxed in enum variants. Only for simple
    ADTs (no type args) defined in our crate. -/
def fromBoxImpls (tys : List RustTy) : List RustItem :=
  tys.filterMap fun ty =>
    match ty with
    | .adt path [] =>
      some (.impl_ {
        trait_ := some {
          path := .simple "From"
          typeArgs := [.adt ⟨["Box"]⟩ [ty]] }
        ty := path
        methods :=
          [{ vis := .priv
             name := "from"
             params := [.named (.ident "b")
               (.adt ⟨["Box"]⟩ [ty])]
             retTy := some .self_
             body := .block []
               (some (.unaryOp .deref
                 (.ident "b"))) }] })
    | _ => none

/-- Render an enum variant line. -/
private def renderVariant (v : RustVariant) : String :=
  let fields := if v.fields.isEmpty then ""
    else s!"({String.intercalate ", "
      (v.fields.map RustTy.render)})"
  s!"{ind 1}/// {v.doc}\n{ind 1}{v.name}{fields},"

namespace RustEnum
def render (e : RustEnum) : String :=
  let attrLines := e.attrs.map (·.render ++ "\n")
  let variantLines := e.variants.map renderVariant
  s!"/// {e.doc}\n\
     {String.join attrLines}\
     {e.vis.render}enum {e.name} \{\n\
     {String.intercalate "\n" variantLines}\n\
     }"
end RustEnum

namespace RustStruct

/-- Render the struct definition only. -/
def render (s : RustStruct) : String :=
  let attrLines := s.attrs.map (·.render ++ "\n")
  match s.fields with
  | .unnamed fields =>
    let fieldStrs := fields.map fun (v, ty) =>
      s!"{v.render}{ty.render}"
    let body := String.intercalate ", " fieldStrs
    s!"/// {s.doc}\n\
       {String.join attrLines}\
       {s.vis.render}struct {s.name}({body});"
  | .named fields =>
    let fieldLines := fields.map fun (v, n, ty) =>
      s!"{ind 1}{v.render}{n}: {ty.render},"
    s!"/// {s.doc}\n\
       {String.join attrLines}\
       {s.vis.render}struct {s.name} \{\n\
       {String.intercalate "\n" fieldLines}\n\
       }"

/-- Build an inherent `impl` with a `new()` constructor
    for a named-field struct. -/
def newImpl (s : RustStruct) : Option RustImpl :=
  match s.fields with
  | .unnamed _ => none
  | .named fields =>
    let params := fields.map fun (_, n, ty) =>
      RustParam.named (.ident n) (.implInto ty)
    let init := RustExpr.structInit .self_
      (fields.map fun (_, n, _) =>
        (n, RustExpr.methodCall (.path ⟨[n]⟩) "into" []))
    let body := RustExpr.block [] (some init)
    some {
      trait_ := none
      ty := ⟨[s.name]⟩
      methods := [{
        vis := .pub
        name := "new"
        params := params
        retTy := some .self_
        body := body
      }]
    }

end RustStruct

namespace RustImpl
def render (i : RustImpl) : String :=
  let traitStr := match i.trait_ with
    | some t => s!"{t.render} for "
    | none => ""
  let methodStrs := i.methods.map fun f =>
    s!"{ind 1}{RustFn.render 1 f}"
  s!"impl {traitStr}{i.ty.render} \{\n\
     {String.intercalate "\n\n" methodStrs}\n\
     }"
end RustImpl

namespace RustItem
def render : RustItem → String
  | .enum e => e.render
  | .struct_ s => s.render
  | .impl_ i => i.render
  | .fn_ f => RustFn.render 0 f
end RustItem

namespace RustModule

/-- Render a module to a complete Rust source file.
    `siblings` lists other module names in the same crate,
    generating `use crate::<sibling>::*;` imports. -/
def render (m : RustModule)
    (siblings : List String := []) : String :=
  let header := s!"//! {m.doc}\n"
  let siblingImports := siblings.filter (· != m.name)
  let uses := siblingImports.map fun s =>
    s!"#[allow(unused_imports)]\n\
       use crate::{s}::*;"
  let usesStr := if uses.isEmpty then ""
    else String.intercalate "\n" uses ++ "\n"
  let body := m.items.map RustItem.render
  s!"{header}\n{usesStr}\
     {String.intercalate "\n\n" body}\n"

/-- Render the `mod` declaration for `lib.rs`. -/
def modDecl (m : RustModule) : String :=
  s!"pub mod {m.name};"

end RustModule

namespace RustCrate

/-- Render the `Cargo.toml` for this crate. -/
def cargoToml (c : RustCrate) : String :=
  let pkg := [
    "[package]",
    s!"name = \"{c.name}\"",
    s!"version = \"{c.version}\"",
    s!"edition = \"{c.edition}\"",
    s!"description = \"{c.description}\""
  ]
  let depSection := if c.deps.isEmpty then []
    else
      let lb := "{"
      let rb := "}"
      let depLines := c.deps.map fun d =>
        s!"{d.name} = {lb} path = \"{d.path}\" {rb}"
      ["", "[dependencies]"] ++ depLines
  String.intercalate "\n" (pkg ++ depSection) ++ "\n"

/-- Render `lib.rs` with crate attributes, module declarations,
    and re-exports. -/
def libRs (c : RustCrate) : String :=
  let attrs := c.crateAttrs.map fun a => s!"#![{a}]"
  let mods := c.modules.map (·.modDecl)
  let reexports := c.reexports.map fun r =>
    s!"pub use {r};"
  let sections := [attrs, mods, reexports].filter
    (!·.isEmpty)
  String.intercalate "\n\n"
    (sections.map fun s =>
      String.intercalate "\n" s)
    ++ "\n"

/-- All files in the crate as `(relative_path, contents)` pairs. -/
def files (c : RustCrate) : List (String × String) :=
  let cargoFile := ("Cargo.toml", c.cargoToml)
  let libFile := ("src/lib.rs", c.libRs)
  let siblings := c.modules.map (·.name)
  let modFiles := c.modules.map fun m =>
    (s!"src/{m.name}.rs", m.render siblings)
  cargoFile :: libFile :: modFiles

end RustCrate

namespace RustWorkspace

/-- Render the workspace `Cargo.toml`. -/
def cargoToml (w : RustWorkspace) : String :=
  let members := w.members.map fun m => s!"    \"{m}\","
  s!"[workspace]\nresolver = \"2\"\n\
     members = [\n\
     {String.intercalate "\n" members}\n]\n"

end RustWorkspace

/-- Standard derives for auto-generated Rust types. -/
def defaultRustDerives : List String :=
  ["Debug", "Clone", "PartialEq", "Eq", "Hash"]

/-- Convert a camelCase or PascalCase string to
    snake_case. -/
def toSnakeCase (s : String) : String := Id.run do
  let mut result : String := ""
  let mut prevLower := false
  for c in s.toList do
    if c.isUpper then
      if prevLower then result := result.push '_'
      result := result.push c.toLower
      prevLower := false
    else
      result := result.push c
      prevLower := c.isLower
  return result

/-- Map a Lean identifier to a Rust-safe snake_case
    identifier. -/
def leanToRustIdent (s : String) : String :=
  let mapped := match s with
    | "τ" => "ty"
    | "τ₀" => "ty0"
    | "σ" => "sigma"
    | "π" => "pi"
    | other => other
  toSnakeCase mapped

/-- Map a Lean type name to a Rust type name. -/
partial def leanToRustType (s : String) : String :=
  match s with
  | "Nat" => "usize"
  | "String" => "String"
  | "Bool" => "bool"
  | other =>
    if other.startsWith "List " then
      let inner := leanToRustType (other.drop 5).toString
      s!"Vec<{inner}>"
    else if other.startsWith "Option " then
      let inner := leanToRustType (other.drop 7).toString
      s!"Option<{inner}>"
    else other

namespace EnumDef

/-- Convert an `ArgDef`'s type to `RustTy`, wrapping in
    `Box` if self-referential. -/
private def argToRustTy
    (enumName : String) (a : ArgDef) : RustTy :=
  let ft := FType.parse a.typeName
  let rustTy := ft.toRust
  if ft.isRecursiveIn enumName then
    .adt ⟨["Box"]⟩ [rustTy]
  else rustTy

/-- Convert an `EnumDef` to a `RustItem.enum`.
    Variant arguments become tuple fields. Self-referential
    fields are wrapped in `Box<>`. -/
def toRustItem (d : EnumDef) : RustItem :=
  .enum {
    doc := d.doc
    attrs := [.derive defaultRustDerives]
    vis := .pub
    name := d.name
    variants := d.variants.map fun v =>
      { doc := v.doc
        name := capitalise v.name
        fields := v.args.map (argToRustTy d.name) } }

/-- Generate Rust source code for this enum. -/
def toRust (d : EnumDef) : String :=
  d.toRustItem.render

end EnumDef

/-- State monad for generating fresh identifiers. -/
abbrev FreshM := StateM Nat

/-- Generate a fresh identifier like `_v0`, `_v1`, … -/
def fresh : FreshM String := do
  let n ← get
  set (n + 1)
  pure s!"_v{n}"

/-- Generate a fresh `RustExpr.ident`. -/
def freshIdent : FreshM RustExpr := do
  return .ident (← fresh)

/-- Generate a fresh `RustPat.ident`. -/
def freshPat : FreshM RustPat := do
  return .ident (← fresh)

namespace BodyExpr

/-- Convert a `BodyExpr` to a typed `RustExpr` in the
    `FreshM` monad (for generating fresh variable names). -/
partial def toRustExpr
    (retType : FType := .prim .unit)
    : BodyExpr → FreshM RustExpr
  | .var n => pure (.ident (leanToRustIdent n))
  | .emptyList => pure .emptyVec
  | .none_ => pure .none_
  | .some_ e => do
    let inner ← e.toRustExpr retType
    match e with
    | .var n =>
      if n == "true" || n == "false" then
        return .some_ inner
      else return .some_ (.clone inner)
    | _ => return .some_ inner
  | .mkStruct sName args => do
    if sName.isEmpty then
      return .tuple (← args.mapM fun a =>
        a.toRustExpr retType)
    else
      return .call (.path ⟨[sName, "new"]⟩)
        (← args.mapM fun a => do
          match a with
          | .var _ =>
            return .clone (← a.toRustExpr retType)
          | .some_ inner =>
            return .some_
              (.clone (← inner.toRustExpr retType))
          | _ => a.toRustExpr retType)
  | .cons h t => do
    let hExpr := RustExpr.clone
      (← h.toRustExpr retType)
    let tExpr ← t.toRustExpr retType
    let v ← fresh
    return .block
      [ .«let» (.ident v) none .emptyVec
          (mutable := true)
      , .expr (.methodCall (.ident v) "push" [hExpr])
      , .expr (.methodCall (.ident v) "extend"
          [tExpr]) ]
      (some (.ident v))
  | .append l r => do
    let lExpr ← l.toRustExpr retType
    let rExpr ← r.toRustExpr retType
    let v ← fresh
    return .block
      [ .«let» (.ident v) none lExpr
          (mutable := true)
      , .expr (.methodCall (.ident v) "extend"
          [rExpr]) ]
      (some (.ident v))
  | .dot recv method => do
    return .call (.ident (toSnakeCase method))
      [.borrow (← recv.toRustExpr retType)]
  | .flatMap list param body => do
    let listE ← list.toRustExpr retType
    let bodyE ← body.toRustExpr retType
    let vecWild := RustTy.adt ⟨["Vec"]⟩ [.infer]
    pure (.methodCall
      (.methodCall
        (.methodCall listE "iter" [])
        "flat_map" [.closure [param] bodyE])
      "collect" []
      (typeArgs := [vecWild]))
  | .field recv name => do
    return .field (← recv.toRustExpr retType)
      (toSnakeCase name)
  | .index list idx => do
    return .methodCall
      (.methodCall (← list.toRustExpr retType)
        "get"
        [.deref (← idx.toRustExpr retType)])
      "cloned" []
  | .call fn args => do
    return .call (.ident (toSnakeCase fn))
      (← args.mapM fun a => do
        return .borrow (← a.toRustExpr retType))
  | .foldlM fn init list => do
    let rustFn := toSnakeCase
      (if fn.endsWith "Step" then
        (fn.take (fn.length - 4)).toString
      else fn)
    return .methodCall
      (.methodCall (← list.toRustExpr retType)
        "iter" [])
      "try_fold"
      [ ← init.toRustExpr retType
      , .closure ["acc", "x"]
          (.call (.ident rustFn)
            [.borrow (.field (.ident "acc") "ty")
            , .ident "x"])]

/-- Run `toRustExpr` with a fresh counter starting at 0. -/
def toRust
    (retType : FType := .prim .unit)
    (e : BodyExpr) : RustExpr :=
  (e.toRustExpr retType).run' 0

end BodyExpr

namespace FnDef

/-- Convert a `FnDef` to a `RustItem.fn_` using the
    typed Rust AST. -/
def toRustItem (f : FnDef) : RustItem :=
  let params := f.params.map fun p =>
    RustParam.named (.ident (leanToRustIdent p.name))
      (.ref false p.ty.toRustParam)
  let retTy := f.returnType.toRust
  -- Extract inner struct name from return type
  let retType := f.returnType
  let rustName := toSnakeCase f.name
  let re (b : BodyExpr) := b.toRust retType
  let body : RustExpr := match f.body with
    | .matchArms arms =>
      if arms.isEmpty then .todo
      else
        let paramNames := f.params.map
          fun p => leanToRustIdent p.name
        let enumNames := f.params.map (·.typeName)
        let scrutinee :=
          if paramNames.length == 1 then
            RustExpr.ident paramNames.head!
          else .tuple (paramNames.map RustExpr.ident)
        let rustArms := arms.map fun arm =>
          let pats := arm.pat.zip enumNames |>.map
            fun (p, en) => p.toRust en
          let patStr := if pats.length == 1
            then pats.head!
            else s!"({", ".intercalate pats})"
          RustMatchArm.mk (.ident patStr) (re arm.rhs)
        .block []
          (some (.«match» scrutinee rustArms))
    | .doBlock stmts ret =>
      let rustStmts := stmts.map fun s =>
        match s with
        | .let_ n v => RustStmt.«let»
            (.ident (leanToRustIdent n)) none
            (.borrow (re v))
        | .letBind n v => RustStmt.«let»
            (.ident (leanToRustIdent n)) none
            (.try_ (re v))
      .block rustStmts (some (re ret))
  .fn_
    { vis := .pub
      name := rustName
      params := params
      retTy := some retTy
      body := body }

end FnDef

namespace StructDef

/-- Convert a `StructDef` to Rust items: the struct
    itself plus `From<Box<T>>` impls for its field
    types. -/
def toRustItems (s : StructDef) : List RustItem :=
  let fieldTys := s.fields.map fun f => f.ty.toRust
  let rs : RustStruct := {
    doc := s.doc
    attrs := [.derive defaultRustDerives]
    vis := .pub
    name := s.name
    fields := .named (s.fields.map fun f =>
      (.pub, toSnakeCase f.name, f.ty.toRust)) }
  let newImplItems := match rs.newImpl with
    | some impl_ => [.impl_ impl_]
    | none => []
  .struct_ rs :: newImplItems ++ fromBoxImpls fieldTys

end StructDef

/-- Derive the Rust crate name from a Lean module prefix
    (e.g. `MIR` → `"formal-mir"`, `PCG` → `"formal-pcg"`). -/
def crateNameOf (prefix_ : String) : String :=
  s!"formal-{prefix_.toLower}"

/-- Derive the Rust module name from a Lean module's last
    component (e.g. `MIR.Region` → `"region"`). -/
def rustModuleNameOf (mod : Lean.Name) : String :=
  match mod with
  | .str _ s => s.toLower
  | _ => "unknown"

/-- Group registered enums by Lean module prefix. -/
def groupEnumsByCrate
    (enums : List RegisteredEnum)
    : List (String × List RegisteredEnum) :=
  let prefixes := enums.map
    fun e => (e.leanModule.getRoot.toString, e)
  let groups := prefixes.foldl (init := [])
    fun acc (p, e) =>
      match acc.find? (·.1 == p) with
      | some _ => acc.map fun (k, vs) =>
          if k == p then (k, vs ++ [e]) else (k, vs)
      | none => acc ++ [(p, [e])]
  groups

/-- Group registered structs by Lean module prefix. -/
def groupStructsByCrate
    (structs : List RegisteredStruct)
    : List (String × List RegisteredStruct) :=
  let prefixes := structs.map
    fun s => (s.leanModule.getRoot.toString, s)
  let groups := prefixes.foldl (init := [])
    fun acc (p, s) =>
      match acc.find? (·.1 == p) with
      | some _ => acc.map fun (k, vs) =>
          if k == p then (k, vs ++ [s]) else (k, vs)
      | none => acc ++ [(p, [s])]
  groups

/-- Build Rust modules from registered enums, structs, and
    functions sharing a crate prefix. -/
def buildModules
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (extraItems : List (String × RustItem))
    : List RustModule :=
  let allModNames :=
    (enums.map fun e => rustModuleNameOf e.leanModule) ++
    (structs.map fun s => rustModuleNameOf s.leanModule) ++
    (fns.map fun f => rustModuleNameOf f.leanModule)
  let uniqueModNames := allModNames.foldl (init := [])
    fun acc m => if acc.contains m then acc else acc ++ [m]
  uniqueModNames.map fun modName =>
    let modEnums := enums.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modStructs := structs.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modFns := fns.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modExtras := extraItems.filter
      (·.1 == modName) |>.map (·.2)
    let items :=
      modStructs.flatMap (·.structDef.toRustItems) ++
      modEnums.map (·.enumDef.toRustItem) ++
      modFns.map (·.fnDef.toRustItem) ++
      modExtras
    let doc := match modEnums.head? with
      | some e => e.enumDef.doc
      | none => match modStructs.head? with
        | some s => s.structDef.doc
        | none => modName
    { name := modName, doc := doc, items := items }

namespace OrderDef

/-- The `std::cmp::Ordering` path. -/
private def ordPath (variant : String) : RustPath :=
  ⟨["std", "cmp", "Ordering", variant]⟩

/-- Classify a pair as Less, Greater, or incomparable. -/
private inductive CmpResult where
  | less | greater | incomparable

/-- Build a merged match arm from pairs sharing a result. -/
private def mergedArm
    (pairs : List (String × String))
    (result : RustExpr)
    : RustMatchArm :=
  let pats := pairs.map fun (a, b) =>
    RustPat.tuple [.selfVariant a, .selfVariant b]
  .mk (.or pats) result

/-- Generate a `PartialOrd` impl from this order. -/
def toRustPartialOrd (o : OrderDef) : RustItem :=
  let selfTy := RustTy.self_
  let selfRef := RustTy.refTo selfTy
  let retTy := RustTy.adt ⟨["Option"]⟩
    [.adt ⟨["std", "cmp", "Ordering"]⟩ []]
  let equalExpr :=
    RustExpr.some_ (.path (ordPath "Equal"))
  let eqCheck : RustExpr :=
    .«if»
      (.binOp .eq (.path (RustPath.simple "self"))
        (.path (RustPath.simple "other")))
      (.block [.expr (.«return» (some equalExpr))]
        none)
      none
  let classify (a b : String) : CmpResult :=
    let aLeB := o.closure.any
      fun (x, y) => x == a && y == b
    let bLeA := o.closure.any
      fun (x, y) => x == b && y == a
    if aLeB then .less
    else if bLeA then .greater
    else .incomparable
  let pairs := o.elements.flatMap fun a =>
    o.elements.filterMap fun b =>
      if a == b then Option.none
      else some (a, b, classify a b)
  let lessPairs := pairs.filterMap fun (a, b, r) =>
    match r with
    | .less => some (capitalise a, capitalise b)
    | _ => none
  let greaterPairs := pairs.filterMap fun (a, b, r) =>
    match r with
    | .greater => some (capitalise a, capitalise b)
    | _ => none
  let lessExpr :=
    RustExpr.some_ (.path (ordPath "Less"))
  let greaterExpr :=
    RustExpr.some_ (.path (ordPath "Greater"))
  let arms :=
    (if lessPairs.isEmpty then []
     else [mergedArm lessPairs lessExpr])
    ++
    (if greaterPairs.isEmpty then []
     else [mergedArm greaterPairs greaterExpr])
  let wildArm : RustMatchArm :=
    .mk (.tuple [.wild, .wild]) RustExpr.none_
  let matchExpr : RustExpr :=
    .«match»
      (.tuple [.path (RustPath.simple "self"),
               .path (RustPath.simple "other")])
      (arms ++ [wildArm])
  let body : RustExpr :=
    .block [.expr eqCheck] (some matchExpr)
  let partialCmpFn : RustFn :=
    { vis := .priv
      name := "partial_cmp"
      params :=
        [ .selfRef
        , .named (.ident "other") selfRef ]
      retTy := some retTy
      body := body }
  .impl_ {
    trait_ := some { path := .simple "PartialOrd" }
    ty := ⟨[o.enumName]⟩
    methods := [partialCmpFn] }

end OrderDef
