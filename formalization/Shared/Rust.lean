import Shared.RustSyntax
import Shared.EnumDef
import Shared.StructDef
import Shared.FnDef
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

namespace RustPath

/-- Render a path: `std::cmp::Ordering::Less`. -/
def render (p : RustPath) : String :=
  String.intercalate "::" p.segments

end RustPath

namespace RustTy

/-- Render a type expression. -/
def render : RustTy → String
  | .path p => p.render
  | .ref true inner => s!"&mut {inner.render}"
  | .ref false inner => s!"&{inner.render}"
  | .generic base args =>
    let argStrs := args.map RustTy.render
    s!"{base.render}<{String.intercalate ", " argStrs}>"
  | .unit => "()"

end RustTy

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
    | .binOp op lhs rhs =>
      s!"{renderExpr d lhs} {op.render} {renderExpr d rhs}"
    | .tuple elems =>
      let inner := elems.map (renderExpr d)
      s!"({String.intercalate ", " inner})"
    | .methodCall recv method args =>
      let argStrs := args.map (renderExpr d)
      s!"{renderExpr d recv}.{method}({String.intercalate ", " argStrs})"
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
    | .«return» none => "return"
    | .«return» (some e) => s!"return {renderExpr d e}"

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
    | d, .«let» pat ty val =>
      let tyStr := match ty with
        | some t => s!": {t.render}"
        | none => ""
      s!"let {pat.render}{tyStr} = {renderExpr d val};"
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

namespace RustItem

/-- Render an enum variant line. -/
private def renderVariant (v : RustVariant) : String :=
  let fields := if v.fields.isEmpty then ""
    else s!"({String.intercalate ", " v.fields})"
  s!"{ind 1}/// {v.doc}\n{ind 1}{v.name}{fields},"

/-- Render a top-level Rust item. -/
def render : RustItem → String
  | .enum doc attrs vis name variants =>
    let attrLines := attrs.map (·.render ++ "\n")
    let variantLines := variants.map renderVariant
    s!"/// {doc}\n\
       {String.join attrLines}\
       {vis.render}enum {name} \{\n\
       {String.intercalate "\n" variantLines}\n\
       }"
  | .tupleStruct doc attrs vis name fields =>
    let attrLines := attrs.map (·.render ++ "\n")
    let fieldStrs := fields.map fun (v, ty) =>
      s!"{v.render}{ty}"
    let body := String.intercalate ", " fieldStrs
    s!"/// {doc}\n\
       {String.join attrLines}\
       {vis.render}struct {name}({body});"
  | .impl_ trait_ ty methods =>
    let traitStr := match trait_ with
      | some t => s!"{t.render} for "
      | none => ""
    let methodStrs := methods.map fun f =>
      s!"{ind 1}{RustFn.render 1 f}"
    s!"impl {traitStr}{ty.render} \{\n\
       {String.intercalate "\n\n" methodStrs}\n\
       }"
  | .fn_ f => RustFn.render 0 f

end RustItem

namespace RustModule

/-- Render a module to a complete Rust source file.
    `siblings` lists other module names in the same crate,
    generating `use crate::<sibling>::*;` imports. -/
def render (m : RustModule)
    (siblings : List String := []) : String :=
  let header := s!"//! {m.doc}\n"
  let uses := siblings.filter (· != m.name) |>.map
    fun s => s!"#[allow(unused_imports)]\nuse crate::{s}::*;"
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

/-- Map a Lean identifier to a Rust-safe identifier. -/
def leanToRustIdent : String → String
  | "τ" => "ty"
  | "σ" => "sigma"
  | other => other

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

/-- Wrap a Rust type in `Box<>` if it references the parent
    enum name (directly or inside `Vec<>`). -/
private def boxIfRecursive
    (enumName : String) (ty : String) : String :=
  let rustTy := leanToRustType ty
  if rustTy == enumName then s!"Box<{rustTy}>"
  else rustTy

/-- Convert an `EnumDef` to a `RustItem.enum`.
    Variant arguments become tuple fields. Self-referential
    fields are wrapped in `Box<>`. -/
def toRustItem (d : EnumDef) : RustItem :=
  .enum d.doc [.derive defaultRustDerives] .pub d.name
    (d.variants.map fun v =>
      { doc := v.doc
        name := capitalise v.name
        fields := v.args.map
          fun a => boxIfRecursive d.name a.typeName })

/-- Generate Rust source code for this enum. -/
def toRust (d : EnumDef) : String :=
  d.toRustItem.render

end EnumDef

namespace FnDef

/-- Convert a `FnDef` to a `RustItem.fn_` with a match
    body derived from the function's match arms. -/
def toRustItem (f : FnDef) : RustItem :=
  let params := f.params.map fun p =>
    RustParam.named (.ident (leanToRustIdent p.name))
      (.ref false (.named (leanToRustType p.typeName)))
  let retTy := RustTy.named (leanToRustType f.returnType)
  let bodyStr := if f.body.isEmpty then "todo!()"
    else
      let paramName := match f.params.head? with
        | some p => leanToRustIdent p.name
        | none => "_x"
      let enumName := match f.params.head? with
        | some p => p.typeName
        | none => "Self"
      let arms := f.body.map fun arm =>
        let pat := " ".intercalate
          (arm.pat.map (·.toRust enumName))
        let rhs := arm.rhs.toRust f.name
        s!"        {pat} => {rhs},"
      s!"match {paramName} {lb}\n\
         {"\n".intercalate arms}\n    {rb}"
  .fn_
    { vis := .pub
      name := f.name
      params := params
      retTy := some retTy
      body := .block [] (some (.path ⟨[bodyStr]⟩)) }
  where lb := "{" ; rb := "}"

end FnDef

namespace StructDef

/-- Convert a `StructDef` to a `RustItem.tupleStruct`. -/
def toRustItem (s : StructDef) : RustItem :=
  .tupleStruct s.doc [.derive defaultRustDerives] .pub s.name
    (s.fields.map fun f => (.pub, leanToRustType f.typeName))

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
      modStructs.map (·.structDef.toRustItem) ++
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
  let retTy := RustTy.generic ⟨["Option"]⟩
    [.path (⟨["std", "cmp", "Ordering"]⟩)]
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
  .impl_
    (some ⟨["PartialOrd"]⟩) ⟨[o.enumName]⟩
    [partialCmpFn]

end OrderDef
