import Core.Export.RustSyntax
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.FnDef
import Core.Dsl.DslType
import Core.Dsl.Types.OrderDef
import Core.Dsl.Types.PropertyDef
import Core.Registry
import Core.Export.Lean

-- ══════════════════════════════════════════════
-- DSLPrimTy / DSLType → Rust conversions
-- ══════════════════════════════════════════════

namespace DSLPrimTy

/-- Convert to a `RustBuiltinTy`. -/
def toRust : DSLPrimTy → RustBuiltinTy
  | .nat => .usize
  | .string => .string
  | .bool => .bool
  | .unit => .unit
  | .u8 => .u8
  | .u16 => .u16
  | .u32 => .u32
  | .u64 => .u64
  | .usize => .usize

/-- Render a primitive to a Rust type string. -/
def toRustStr (p : DSLPrimTy) : String := p.toRust.render

end DSLPrimTy

namespace DSLType

mutual

/-- Convert to a typed `RustTy`. -/
partial def toRust : DSLType → RustTy
  | .prim p => .builtin p.toRust
  | .named n => .named n.name
  | .option t => .option t.toRust
  | .list t => .adt ⟨[⟨"Vec"⟩]⟩ [t.toRust]
  | .set t => .adt ⟨[⟨"HashSet"⟩]⟩ [t.toRust]
  | .map k v =>
    .adt ⟨[⟨"HashMap"⟩]⟩ [k.toRust, v.toRust]
  | .tuple ts =>
    .named s!"({", ".intercalate (ts.map fun t => t.toRust.render)})"
  | .arrow a b =>
    -- Render `A → B → C` as `Box<dyn Fn(A, B) -> C>`.
    let (argStrs, retStr) := arrowFlatten (.arrow a b)
    .named s!"Box<dyn Fn({", ".intercalate argStrs}) -> {retStr}>"

/-- Flatten a right-associated arrow chain into rendered
    argument strings and a rendered return string. -/
partial def arrowFlatten : DSLType → List String × String
  | .arrow x y =>
    let (xs, ret) := arrowFlatten y
    (x.toRust.render :: xs, ret)
  | t => ([], t.toRust.render)

end

/-- Convert to a Rust parameter type. Lists become
    slices (`&[T]`) for pattern-matching support. -/
def toRustParam : DSLType → RustTy
  | .prim p => .builtin p.toRust
  | .named n => .named n.name
  | .option t => .option t.toRust
  | .list t => .slice t.toRust
  | .set t =>
    .ref false (.adt ⟨[⟨"HashSet"⟩]⟩ [t.toRust])
  | .map k v =>
    .ref false (.adt ⟨[⟨"HashMap"⟩]⟩ [k.toRust, v.toRust])
  | .tuple ts =>
    .named s!"({", ".intercalate (ts.map fun t => t.toRust.render)})"
  | .arrow a b =>
    let (argStrs, retStr) := arrowFlatten (.arrow a b)
    .named s!"Box<dyn Fn({", ".intercalate argStrs}) -> {retStr}>"

/-- Render a type to a Rust type string. -/
def toRustStr (t : DSLType) : String := t.toRust.render

/-- Whether this type contains an arrow (function) type.
    Structs with arrow-typed fields cannot derive standard
    traits like `PartialEq`, `Eq`, `Hash`, `Clone`. -/
partial def containsArrow : DSLType → Bool
  | .arrow _ _ => true
  | .prim _ => false
  | .named _ => false
  | .option t => t.containsArrow
  | .list t => t.containsArrow
  | .set t => t.containsArrow
  | .map k v => k.containsArrow || v.containsArrow
  | .tuple ts => ts.any containsArrow

end DSLType

-- ══════════════════════════════════════════════

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
  | .and => "&&" | .or => "||" | .add => "+" | .sub => "-"
  | .mul => "*" | .div => "/"

end RustBinOp

namespace RustPat

/-- Render a pattern. -/
partial def render : RustPat → String
  | .ident n => n.val
  | .wild => "_"
  | .tuple ps =>
    let inner := ps.map RustPat.render
    s!"({String.intercalate ", " inner})"
  | .path p => p.render
  | .ref inner => s!"&{inner.render}"
  | .or pats =>
    String.intercalate " | " (pats.map RustPat.render)
  | .struct_ sp fields rest =>
    let fieldStrs := fields.map fun (f, p) =>
      if p == .ident f then f.val
      else s!"{f.val}: {p.render}"
    let restStr := if rest then
      if fields.isEmpty then ".." else ", .."
    else ""
    s!"{sp.render} \{ \
       {", ".intercalate fieldStrs}{restStr} }"
  | .pathArgs pp args =>
    if args.isEmpty then pp.render
    else
      let argStrs := args.map RustPat.render
      s!"{pp.render}\
         ({", ".intercalate argStrs})"
  | .slice elems rest =>
    let elemStrs := elems.map RustPat.render
    let restStr := match rest with
      | some (.ident n) => [s!"{n.val} @ .."]
      | some .wild => [".."]
      | some p => [s!"{p.render} @ .."]
      | none => []
    s!"[{", ".intercalate (elemStrs ++ restStr)}]"

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
    s!"#[derive({String.intercalate ", " (traits.map (·.val))})]"
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
      let isArith (o : RustBinOp) :=
        o == .add || o == .sub || o == .mul || o == .div
      let wrap (e : RustExpr) :=
        match e with
        | .binOp op' .. =>
          if isArith op && isArith op'
          then s!"({renderExpr d e})" else renderExpr d e
        | _ => renderExpr d e
      s!"{wrap lhs} {op.render} {wrap rhs}"
    | .tuple elems =>
      let inner := elems.map (renderExpr d)
      s!"({String.intercalate ", " inner})"
    | .methodCall recv method args typeArgs =>
      let argStrs := args.map (renderExpr d)
      let turbo := if typeArgs.isEmpty then ""
        else s!"::<{String.intercalate ", "
          (typeArgs.map RustTy.render)}>"
      s!"{renderExpr d recv}.{method.val}{turbo}({String.intercalate ", " argStrs})"
    | .field recv name =>
      s!"{renderExpr d recv}.{name.val}"
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
    | .ref_ false e =>
      match e with
      | .binOp .. | .unaryOp .. | .ref_ .. =>
        s!"&({renderExpr d e})"
      | _ => s!"&{renderExpr d e}"
    | .ref_ true e =>
      match e with
      | .binOp .. | .unaryOp .. | .ref_ .. =>
        s!"&mut ({renderExpr d e})"
      | _ => s!"&mut {renderExpr d e}"
    | .«return» none => "return"
    | .«return» (some e) => s!"return {renderExpr d e}"
    | .try_ e => s!"{renderExpr d e}?"
    | .closure params body =>
      let ps := String.intercalate ", " (params.map (·.val))
      s!"|{ps}| {renderExpr d body}"
    | .structInit path fields =>
      let i := ind (d + 1)
      let fieldStrs := fields.map fun (n, e) =>
        s!"{i}{n.val}: {renderExpr (d + 1) e},"
      s!"{path.render} \{\n\
         {String.intercalate "\n" fieldStrs}\n\
         {ind d}}"
    | .index recv idx =>
      s!"{renderExpr d recv}[{renderExpr d idx}]"
    | .raw s => s
    | .cast e ty =>
      s!"({renderExpr d e} as {ty.render})"

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
    | d, .assert_ e =>
      s!"assert!({renderExpr d e});"
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
  s!"{vis}fn {f.name.val}({paramStr}){retStr} {bodyStr}"

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
          typeArgs := [.adt ⟨[⟨"Box"⟩]⟩ [ty]] }
        ty := path
        methods :=
          [{ vis := .priv
             name := ⟨"from"⟩
             params := [.named (.ident ⟨"b"⟩)
               (.adt ⟨[⟨"Box"⟩]⟩ [ty])]
             retTy := some .self_
             body := .block []
               (some (.unaryOp .deref
                 (.ident ⟨"b"⟩))) }] })
    | _ => none

/-- Render an enum variant line. -/
private def renderVariant (v : RustVariant) : String :=
  let fields := if v.fields.isEmpty then ""
    else s!"({String.intercalate ", "
      (v.fields.map RustTy.render)})"
  s!"{ind 1}/// {v.doc}\n{ind 1}{v.name.val}{fields},"

/-- Render the generic parameter list: empty string for no
    generics, `<A, B>` otherwise. -/
private def renderGenerics (gs : List RustIdent) : String :=
  if gs.isEmpty then ""
  else s!"<{String.intercalate ", " (gs.map (·.val))}>"

namespace RustEnum
def render (e : RustEnum) : String :=
  let attrLines := e.attrs.map (·.render ++ "\n")
  let variantLines := e.variants.map renderVariant
  let gen := renderGenerics e.generics
  s!"/// {e.doc}\n\
     {String.join attrLines}\
     {e.vis.render}enum {e.name.val}{gen} \{\n\
     {String.intercalate "\n" variantLines}\n\
     }"
end RustEnum

namespace RustStruct

/-- Render the struct definition only. -/
def render (s : RustStruct) : String :=
  let attrLines := s.attrs.map (·.render ++ "\n")
  let gen := renderGenerics s.generics
  match s.fields with
  | .unnamed fields =>
    let fieldStrs := fields.map fun (v, ty) =>
      s!"{v.render}{ty.render}"
    let body := String.intercalate ", " fieldStrs
    s!"/// {s.doc}\n\
       {String.join attrLines}\
       {s.vis.render}struct {s.name.val}{gen}({body});"
  | .named fields =>
    let fieldLines := fields.map fun (v, n, ty) =>
      s!"{ind 1}{v.render}{n.val}: {ty.render},"
    s!"/// {s.doc}\n\
       {String.join attrLines}\
       {s.vis.render}struct {s.name.val}{gen} \{\n\
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
        (n, RustExpr.methodCall (.path ⟨[n]⟩) ⟨"into"⟩ []))
    let body := RustExpr.block [] (some init)
    some {
      trait_ := none
      ty := ⟨[s.name]⟩
      methods := [{
        vis := .pub
        name := ⟨"new"⟩
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
  | .raw s => s
end RustItem

namespace RustModule

/-- Render a module to a complete Rust source file.
    `siblings` lists other module names in the same crate,
    generating `use crate::<sibling>::*;` imports. -/
def render (m : RustModule)
    (siblings : List String := []) : String :=
  let header := s!"//! {m.doc}\n"
  let siblingImports := siblings.filter (· != m.name.val)
  let uses := siblingImports.flatMap fun s =>
    [ s!"#[allow(unused_imports)]\n\
         use crate::{s}::*;"
    , s!"#[allow(unused_imports)]\n\
         use crate::{s};" ]
  let extraUseLines := m.extraUses.map fun u =>
    s!"use {u};"
  let allUses := uses ++ extraUseLines
  let usesStr := if allUses.isEmpty then ""
    else String.intercalate "\n" allUses ++ "\n"
  let body := m.items.map RustItem.render
  s!"{header}\n{usesStr}\
     {String.intercalate "\n\n" body}\n"

/-- Render the `mod` declaration for `lib.rs`. -/
def modDecl (m : RustModule) : String :=
  s!"pub mod {m.name.val};"

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
  let siblings := c.modules.map (·.name.val)
  let modFiles := c.modules.map fun m =>
    (s!"src/{m.name.val}.rs", m.render siblings)
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
def defaultRustDerives : List RustIdent :=
  [⟨"Debug"⟩, ⟨"Clone"⟩, ⟨"PartialEq"⟩, ⟨"Eq"⟩, ⟨"Hash"⟩]

/-- Convert a camelCase or PascalCase string to
    snake_case. -/
def toSnakeCase (s : String) : String := Id.run do
  let mut result : String := ""
  let mut prevLower := false
  for c in s.toList do
    if c == '\'' then
      result := result ++ "_prime"
    else if c.isUpper then
      if prevLower then result := result.push '_'
      result := result.push c.toLower
      prevLower := false
    else
      result := result.push c
      prevLower := c.isLower
  return result

/-- Map a Lean identifier to a Rust-safe snake_case
    identifier. -/
private def leanToRustIdent (s : String) : RustIdent :=
  let mapped := match s with
    | "τ" => "ty"
    | "τ₀" => "ty0"
    | "σ" => "sigma"
    | "π" => "pi"
    | other => other
  ⟨toSnakeCase mapped⟩

namespace DSLType

/-- Whether this type needs `Box` wrapping in Rust
    when it appears inside the definition of `enumTy`
    (i.e. it's self-referential). -/
def needsRustBoxIn : DSLType → DSLType → Bool
  | .named n, enumTy => enumTy == .named n
  | .option t, enumTy => t.needsRustBoxIn enumTy
  | .list _, _ => false  -- Vec handles indirection
  | .set _, _ => false   -- HashSet handles indirection
  | .map _ _, _ => false -- HashMap handles indirection
  | .prim _, _ => false
  | .tuple _, _ => false
  | .arrow _ _, _ => false -- already a Box<dyn Fn ...>

end DSLType

namespace EnumDef

/-- Convert an `ArgDef`'s type to `RustTy`, wrapping in
    `Box` if self-referential. -/
private def argToRustTy
    (enumTy : DSLType) (a : ArgDef) : RustTy :=
  let ft := a.type
  let rustTy := ft.toRust
  if ft.needsRustBoxIn enumTy then
    .adt ⟨[⟨"Box"⟩]⟩ [rustTy]
  else rustTy

/-- Convert an `EnumDef` to a `RustItem.enum`.
    Variant arguments become tuple fields. Self-referential
    fields are wrapped in `Box<>`. -/
def toRustItem (d : EnumDef) : RustItem :=
  .enum {
    doc := d.doc.toPlainText
    attrs := [.derive defaultRustDerives]
    vis := .pub
    name := ⟨d.name.name⟩
    generics := d.typeParams.map (⟨·⟩)
    variants := d.variants.map fun v =>
      { doc := v.doc
        name := ⟨capitalise v.name.name⟩
        fields := v.args.map
          (argToRustTy (.named d.name)) } }

/-- Generate Rust source code for this enum. -/
def toRust (d : EnumDef) : String :=
  d.toRustItem.render

end EnumDef

/-- Information about a registered function's
    qualified Rust location. -/
structure QualifiedFn where
  /-- The Lean module root prefix (e.g. "MIR"). -/
  leanPrefix : String
  /-- The Rust module name (e.g. "ty"). -/
  rustModule : String
  /-- The Rust function name in snake_case. -/
  rustFnName : String

/-- Context for Rust expression generation. -/
structure RustExprCtxt where
  /-- Known qualified function calls
      (e.g. "Ty.bytes" → its Rust location). -/
  knownFns : List (String × QualifiedFn) := []
  /-- The current crate's Lean prefix
      (e.g. "MIR", "OpSem"). -/
  currentPrefix : String := ""
  /-- The current module name (e.g. "ty"). -/
  currentModule : String := ""

instance : Inhabited RustExprCtxt where
  default :=
    { knownFns := []
      currentPrefix := ""
      currentModule := "" }

/-- State monad for generating fresh identifiers. -/
abbrev FreshM := StateM Nat

/-- Generate a fresh identifier like `_v0`, `_v1`, … -/
def fresh : FreshM RustIdent := do
  let n ← get
  set (n + 1)
  pure ⟨s!"_v{n}"⟩

/-- Generate a fresh `RustExpr.ident`. -/
def freshIdent : FreshM RustExpr := do
  return .ident (← fresh)

/-- Generate a fresh `RustPat.ident`. -/
def freshPat : FreshM RustPat := do
  return .ident (← fresh)

namespace BodyPat

/-- Convert a `BodyPat` to a typed `RustPat`.
    `enumName` is the enum type name (for qualifying
    variant paths). `structFields` returns field names
    for struct destructuring. -/
partial def toRustPat (enumName : String)
    (structFields : String → Option (List String)
      := fun _ => none)
    : BodyPat → RustPat
  | .wild => .wild
  | .var n => .ident (leanToRustIdent n)
  | .ctor "⟨⟩" args =>
    match structFields enumName with
    | some fields =>
      let bindings := (fields.map (⟨·⟩ : String → RustIdent)).zip
        (args.map (toRustPat "" structFields))
      .struct_ (.simple enumName) bindings false
    | none =>
      .tuple (args.map (toRustPat "" structFields))
  | .ctor n args =>
    let rustArgs :=
      args.map (toRustPat enumName structFields)
    match n.splitOn "." with
    | [en, v] =>
      .pathArgs ⟨[⟨en⟩, ⟨capitalise v⟩]⟩ rustArgs
    | _ =>
      let capName := capitalise n
      if enumName.isEmpty then
        .pathArgs (.simple capName) rustArgs
      else
        .pathArgs ⟨[⟨enumName⟩, ⟨capName⟩]⟩ rustArgs
  | .nil => .slice [] none
  | .cons h tail =>
    let stripParens (s : String) : String :=
      let s := s.trimAscii.toString
      if s.startsWith "(" && s.endsWith ")" then
        (s.drop 1 |>.dropEnd 1).trimAscii.toString
      else s
    let elemName := if enumName.startsWith "List "
      then stripParens (enumName.drop 5).toString
      else stripParens enumName
    -- Collect a chain of cons followed by nil/wild/var
    let rec collect : BodyPat → List BodyPat × Option BodyPat
      | .nil => ([], none)
      | .cons h' t =>
        let (hs, rest) := collect t
        (h' :: hs, rest)
      | other => ([], some other)
    let (headPats, restTail) := collect (.cons h tail)
    let rustHeads := headPats.map
      fun p => p.toRustPat elemName structFields
    let restPat := restTail.map fun t => match t with
      | .var rest => RustPat.ident (leanToRustIdent rest)
      | .wild => RustPat.wild
      | _ => t.toRustPat (s!"List ({elemName})") structFields
    .slice rustHeads restPat
  | .natLit n => .path (.simple (toString n))

end BodyPat

namespace DslExpr

/-- Algebra for `toRustExpr` under `DslExpr.paraM`: each recursive child
    is a pair `(origSubterm, rustTranslation)`, letting the algebra inspect
    the original DSL subterm when deciding whether to wrap children in
    `.clone`, etc. `recur` is the top-level `toRustExpr`, used by the
    `.mkStruct` arm to re-lower an inner `DslExpr` whose already-computed
    `.some_`-wrapped Rust translation is not what we want there. -/
private partial def toRustAlg (recur : DslExpr → FreshM RustExpr) :
    DslExprF (DslExpr × RustExpr) → FreshM RustExpr
  | .var n => pure (.ident (leanToRustIdent n))
  | .natLit n => pure (.raw s!"{n}usize")
  | .true_ => pure (.litBool true)
  | .false_ => pure (.litBool false)
  | .emptyList => pure .emptyVec
  | .none_ => pure .none_
  | .some_ (e, inner) => do
    match e with
    | .true_ | .false_ => return .some_ inner
    | .var _ => return .some_ (.clone inner)
    | _ => return .some_ inner
  | .mkStruct sName args => do
    if sName.isEmpty then
      return .tuple (← args.mapM fun (a, rustA) =>
        match a with
        | .var _ => pure (.clone rustA)
        | .field _ _ => pure (.clone rustA)
        | _ => pure rustA)
    else
      return .call (.path ⟨[⟨sName⟩, ⟨"new"⟩]⟩)
        (← args.mapM fun (a, rustA) => do
          match a with
          | .var _ => pure (.clone rustA)
          | .field _ _ => pure (.clone rustA)
          | .some_ inner =>
            -- Re-run recursion on `inner` since we need the Rust translation
            -- of the inner expression, not the already-wrapped `.some_`.
            let rustInner ← recur inner
            pure (.some_ (.clone rustInner))
          | _ => pure rustA)
  | .cons (_, hExpr) (_, tExpr) => do
    let hExpr := RustExpr.clone hExpr
    let v ← fresh
    return .block
      [ .«let» (.ident v) none .emptyVec
          (mutable := true)
      , .expr (.methodCall (.ident v) ⟨"push"⟩ [hExpr])
      , .expr (.methodCall (.ident v) ⟨"extend"⟩
          [.methodCall
            (.methodCall tExpr ⟨"iter"⟩ [])
            ⟨"cloned"⟩ []]) ]
      (some (.ident v))
  | .append (_, lExpr) (_, rExpr) => do
    let v ← fresh
    return .block
      [ .«let» (.ident v) none
          (.methodCall lExpr ⟨"to_vec"⟩ [])
          (mutable := true)
      , .expr (.methodCall (.ident v) ⟨"extend"⟩
          [.methodCall
            (.methodCall rExpr ⟨"iter"⟩ [])
            ⟨"cloned"⟩ []]) ]
      (some (.ident v))
  | .dot (_, rustRecv) method => do
    match method with
    | "toNat" =>
      return .cast (.unaryOp .deref rustRecv)
        (.builtin .usize)
    | "length" =>
      return .methodCall rustRecv ⟨"len"⟩ []
    | "toList" =>
      let vecWild := RustTy.adt ⟨[⟨"Vec"⟩]⟩ [.infer]
      return .methodCall
        (.methodCall rustRecv ⟨"into_iter"⟩ [])
        ⟨"collect"⟩ [] (typeArgs := [vecWild])
    | "toSet" =>
      let hsWild := RustTy.adt ⟨[⟨"HashSet"⟩]⟩ [.infer]
      return .methodCall
        (.methodCall rustRecv ⟨"into_iter"⟩ [])
        ⟨"collect"⟩ [] (typeArgs := [hsWild])
    | _ =>
      return .call (.identStr (toSnakeCase method))
        [.borrow rustRecv]
  | .lambda param (_, bodyE) =>
    pure (.closure [leanToRustIdent param.name] bodyE)
  | .flatMap (_, listE) (_, fnE) =>
    let vecWild := RustTy.adt ⟨[⟨"Vec"⟩]⟩ [.infer]
    pure (.methodCall
      (.methodCall
        (.methodCall listE ⟨"iter"⟩ [])
        ⟨"flat_map"⟩ [fnE])
      ⟨"collect"⟩ []
      (typeArgs := [vecWild]))
  | .map (_, listE) (_, fnE) =>
    let vecWild := RustTy.adt ⟨[⟨"Vec"⟩]⟩ [.infer]
    pure (.methodCall
      (.methodCall
        (.methodCall listE ⟨"iter"⟩ [])
        ⟨"map"⟩ [fnE])
      ⟨"collect"⟩ []
      (typeArgs := [vecWild]))
  | .field (_, rustRecv) name =>
    pure (.field rustRecv ⟨toSnakeCase name⟩)
  | .index (_, listE) (_, idxE) =>
    pure (.index listE idxE)
  | .indexBang (_, listE) (_, idxE) =>
    pure (.index listE idxE)
  | .call (origFn, _) args => do
    let filtered := args.filter fun (origA, _) =>
      match origA with
      | .sorryProof | .leanProof _ => false
      | _ => true
    match origFn with
    | .var fn =>
      match fn.splitOn "." with
      | [en, v] =>
        let vStr := capitalise v
        let path : RustPath := ⟨[⟨en⟩, ⟨vStr⟩]⟩
        return .call (.path path)
          (← filtered.mapM fun (a, rustA) =>
            match a with
            | .natLit n => pure (.raw (toString n))
            | .var _ => pure (.clone rustA)
            | .field _ _ => pure (.clone rustA)
            | _ => pure rustA)
      | _ =>
        return .call (.identStr (toSnakeCase fn))
          (← filtered.mapM fun (_, rustA) =>
            pure (.borrow rustA))
    | _ =>
      let fnE ← recur origFn
      return .call fnE
        (← filtered.mapM fun (_, rustA) =>
          pure (.borrow rustA))
  | .foldlM (origFn, _) (_, initE) (_, listE) =>
    let rustFn := match origFn with
      | .var n => toSnakeCase n
      | _ => reprStr origFn
    pure (.methodCall
      (.methodCall listE ⟨"iter"⟩ [])
      ⟨"try_fold"⟩
      [ initE
      , .closure [⟨"acc"⟩, ⟨"x"⟩]
          (.call (.identStr rustFn)
            [.borrow (.field (.identStr "acc") ⟨"ty"⟩)
            , .identStr "x"])])
  | .lt (_, l) (_, r) => pure (.binOp .lt l r)
  | .le (_, l) (_, r) => pure (.binOp .le l r)
  | .ineqChain ops es =>
    let rExprs := es.map Prod.snd
    let opToRust : IneqOp → RustBinOp
      | .lt => .lt | .le => .le
    let pairs := ops.zip (rExprs.zip (rExprs.drop 1))
    let comparisons := pairs.map fun (op, l, r) =>
      RustExpr.binOp (opToRust op) l r
    match comparisons with
    | [] => pure (.raw "true")
    | [c] => pure c
    | c :: cs => pure (cs.foldl
        (fun acc x => .binOp .and acc x) c)
  | .add (_, l) (_, r) => pure (.binOp .add l r)
  | .sub (_, l) (_, r) => pure (.binOp .sub l r)
  | .mul (_, l) (_, r) => pure (.binOp .mul l r)
  | .div (_, l) (_, r) => pure (.binOp .div l r)
  | .setAll (_, setE) param (_, bodyE) =>
    pure (.methodCall
      (.methodCall setE ⟨"iter"⟩ [])
      ⟨"all"⟩ [.closure [⟨param⟩] bodyE])
  | .emptySet =>
    pure (.call (.path ⟨[⟨"HashSet"⟩, ⟨"new"⟩]⟩) [])
  | .setSingleton (_, eE) => do
    let eExpr := RustExpr.clone eE
    let v ← fresh
    return .block
      [ .«let» (.ident v) none
          (.call (.path ⟨[⟨"HashSet"⟩, ⟨"new"⟩]⟩) [])
          (mutable := true)
      , .expr (.methodCall (.ident v) ⟨"insert"⟩
          [eExpr]) ]
      (some (.ident v))
  | .setUnion (_, lExpr) (_, rExpr) => do
    let v ← fresh
    return .block
      [ .«let» (.ident v) none lExpr
          (mutable := true)
      , .expr (.methodCall (.ident v) ⟨"extend"⟩
          [rExpr]) ]
      (some (.ident v))
  | .setFlatMap (_, listE) param (_, bodyE) =>
    let hsWild := RustTy.adt ⟨[⟨"HashSet"⟩]⟩ [.infer]
    pure (.methodCall
      (.methodCall
        (.methodCall listE ⟨"iter"⟩ [])
        ⟨"flat_map"⟩ [.closure [⟨param⟩] bodyE])
      ⟨"collect"⟩ []
      (typeArgs := [hsWild]))
  | .and (_, l) (_, r) => pure (.binOp .and l r)
  | .or (_, l) (_, r) => pure (.binOp .or l r)
  | .implies _ _ => pure (.raw "/* implication omitted */")
  | .forall_ _ _ => pure (.raw "/* forall omitted */ true")
  | .sorryProof => pure (.raw "/* sorry */")
  | .leanProof _ => pure (.raw "/* proof omitted */")
  | .match_ (_, scrutExpr) arms => do
    let rustArms := arms.map fun (pats, (origRhs, rustRhs)) =>
      let pat := if pats.length == 1
        then pats.head!.toRustPat ""
        else .tuple (pats.map (·.toRustPat ""))
      let rhsExpr := match origRhs with
        | .var _ => RustExpr.clone rustRhs
        | _ => rustRhs
      RustMatchArm.mk pat rhsExpr
    pure (.«match» scrutExpr rustArms)
  | .letIn name (_, vExpr) (_, bExpr) =>
    pure (.block
      [ .«let» (.ident (leanToRustIdent name.name)) none
          (.borrow vExpr) (mutable := false) ]
      (some bExpr))
  | .letBindIn name (_, vExpr) (_, bExpr) =>
    pure (.block
      [ .«let» (.ident (leanToRustIdent name)) none
          (.try_ (.clone vExpr)) (mutable := false) ]
      (some bExpr))
  | .ifThenElse (_, cExpr) (_, tExpr) (_, eExpr) =>
    let tBlock : RustExpr := match tExpr with
      | .block _ _ => tExpr
      | _ => .block [] (some tExpr)
    let eBlock : RustExpr := match eExpr with
      | .block _ _ => eExpr
      | _ => .block [] (some eExpr)
    pure (.«if» cExpr tBlock (some eBlock))
  | .neq (_, l) (_, r) => pure (.binOp .ne l r)

/-- Convert a `DslExpr` to a typed `RustExpr` in the
    `FreshM` monad (for generating fresh variable names). -/
partial def toRustExpr (e : DslExpr) : FreshM RustExpr :=
  DslExpr.paraM (toRustAlg toRustExpr) e

/-- Run `toRustExpr` with a fresh counter starting at 0. -/
def toRust (e : DslExpr) : RustExpr :=
  e.toRustExpr.run' 0

/-- Resolve a qualified function call name to its Rust
    path given the context. Returns the original name
    unchanged if not a known function. -/
private def resolveQualifiedCall
    (fn : String) (ctx : RustExprCtxt)
    : String :=
  match ctx.knownFns.find? (·.1 == fn) with
  | some (_, qfn) =>
    if qfn.rustModule == ctx.currentModule then
      qfn.rustFnName
    else if qfn.leanPrefix == ctx.currentPrefix then
      s!"{qfn.rustModule}::{qfn.rustFnName}"
    else
      let c := s!"formal_{qfn.leanPrefix.toLower}"
      s!"{c}::{qfn.rustModule}::{qfn.rustFnName}"
  | none => fn

/-- Rewrite dotted function calls in a `DslExpr` tree.
    Known qualified function names (e.g. `"Ty.bytes"`) are
    replaced with their Rust-qualified path (e.g.
    `"ty::bytes"`), converting them from the dotted-call
    branch (enum variant) to the fallback branch (function
    call) in `toRustExpr`. -/
def qualifyFnCalls
    (ctx : RustExprCtxt) (e : DslExpr) : DslExpr :=
  e.transform fun
    | .call (.var fn) args =>
      match fn.splitOn "." with
      | [_, _] =>
        .call (.var (resolveQualifiedCall fn ctx)) args
      | _ => .call (.var fn) args
    | other => other

end DslExpr

namespace FnDef

/-- Convert a `FnDef` to a `RustItem.fn_` using the
    typed Rust AST. -/
def toRustItem (f : FnDef)
    (structFields : String → Option (List String)
      := fun _ => none)
    (ctx : RustExprCtxt := default)
    : RustItem :=
  let params := f.params.map fun p =>
    RustParam.named (.ident (leanToRustIdent p.name))
      (.ref false p.ty.toRustParam)
  let retTy := f.returnType.toRust
  let rustName : RustIdent := ⟨toSnakeCase f.name⟩
  let qualify := DslExpr.qualifyFnCalls ctx
  let re (b : DslExpr) := (qualify b).toRust
  let paramNames := f.params.map
    fun p => leanToRustIdent p.name
  let assertStmts := f.preconditions.map fun pc =>
    let args := pc.args.map fun a =>
      RustExpr.ident (leanToRustIdent a)
    RustStmt.assert_
      (.call (.identStr (toSnakeCase pc.name)) args)
  let body : RustExpr := match f.body with
    | .matchArms arms =>
      if arms.isEmpty then .todo
      else
        let enumNames := f.params.map (·.typeName)
        let scrutinee :=
          if paramNames.length == 1 then
            RustExpr.ident paramNames.head!
          else .tuple (paramNames.map RustExpr.ident)
        let rustArms := arms.map fun arm =>
          let pats := arm.pat.zip enumNames |>.map
            fun (p, en) => p.toRustPat en structFields
          let pat := if pats.length == 1
            then pats.head!
            else .tuple pats
          RustMatchArm.mk pat (re arm.rhs)
        let unreachableArm :=
          RustMatchArm.mk .wild (.raw "unreachable!()")
        .block assertStmts
          (some (.«match» scrutinee
            (rustArms ++ [unreachableArm])))
    | .expr body =>
      .block assertStmts (some (re body))
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
  let selfTy : RustTy := .adt (.simple s.name) []
  let fieldTys := [selfTy]
  let isCopyPrim : DSLType → Bool
    | .prim .string => false
    | .prim .unit => false
    | .prim _ => true
    | _ => false
  let allCopy := s.fields.all fun f => isCopyPrim f.ty
  let hasUnhashable := s.fields.any fun f =>
    match f.ty with
    | .map _ _ | .set _ => true | _ => false
  -- Closure trait objects (`Box<dyn Fn(..)>`) can only
  -- derive `Debug`-less traits; drop the default derives
  -- and skip the `From<Box<T>>` impl when the struct has
  -- any function-typed field.
  let hasArrow := s.fields.any fun f => f.ty.containsArrow
  let isGeneric := !s.typeParams.isEmpty
  let baseDerives := if hasUnhashable
    then defaultRustDerives.filter (·.val != "Hash")
    else defaultRustDerives
  let baseDerives := if hasArrow then [] else baseDerives
  let derives := if allCopy && !hasArrow && !isGeneric
    then baseDerives ++ [⟨"Copy"⟩]
    else baseDerives
  let rs : RustStruct := {
    doc := s.doc.toPlainText
    attrs := if derives.isEmpty then []
             else [.derive derives]
    vis := .pub
    name := ⟨s.name⟩
    generics := s.typeParams.map (⟨·⟩)
    fields := .named (s.fields.map fun f =>
      (.pub, ⟨toSnakeCase f.name⟩, f.ty.toRust)) }
  -- Skip inherent `new()` and `From<Box<T>>` impls for
  -- generic structs: the former would need `impl Into<T>`
  -- on type parameters and the latter would need per-param
  -- blanket impls, both of which are out of scope here.
  let newImplItems :=
    if hasArrow || isGeneric then []
    else match rs.newImpl with
      | some impl_ => [.impl_ impl_]
      | none => []
  let boxImpls :=
    if hasArrow || isGeneric then []
    else fromBoxImpls fieldTys
  .struct_ rs :: newImplItems ++ boxImpls

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

/-- Build a `RustExprCtxt` from all registered items. -/
def buildRustExprCtxt
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : RustExprCtxt :=
  let allTypes : List String :=
    (enums.map (·.enumDef.name.name)) ++
    (structs.map (·.structDef.name))
  let addFn (acc : List (String × QualifiedFn))
      (f : FnDef) (leanMod : Lean.Name)
      : List (String × QualifiedFn) :=
    match f.params.head? with
    | some p => match p.ty with
      | .named n =>
        if allTypes.contains n.name then
          let prefix_ := leanMod.getRoot.toString
          let modName := rustModuleNameOf leanMod
          let qfn : QualifiedFn :=
            { leanPrefix := prefix_
              rustModule := modName
              rustFnName := toSnakeCase f.name }
          acc ++ [(s!"{n.name}.{f.name}", qfn)]
        else acc
      | _ => acc
    | none => acc
  let knownFns := fns.foldl
    (fun acc rf => addFn acc rf.fnDef rf.leanModule)
    []
  let knownFns := properties.foldl
    (fun acc rp => addFn acc rp.propertyDef.fnDef
      rp.leanModule)
    knownFns
  { knownFns }

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

/-- Build Rust modules from registered enums, structs,
    functions, and properties sharing a crate prefix. -/
def buildModules
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (extraItems : List (String × RustItem))
    (ctx : RustExprCtxt := default)
    : List RustModule :=
  let allModNames :=
    (enums.map fun e => rustModuleNameOf e.leanModule) ++
    (structs.map fun s => rustModuleNameOf s.leanModule) ++
    (fns.map fun f => rustModuleNameOf f.leanModule) ++
    (properties.map fun p =>
      rustModuleNameOf p.leanModule)
  let uniqueModNames := allModNames.foldl (init := [])
    fun acc m => if acc.contains m then acc else acc ++ [m]
  uniqueModNames.map fun modName =>
    let modEnums := enums.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modStructs := structs.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modFns := fns.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modProps := properties.filter
      (rustModuleNameOf ·.leanModule == modName)
    let modExtras := extraItems.filter
      (·.1 == modName) |>.map (·.2)
    let structFieldLookup : String → Option (List String) :=
      fun name => structs.findSome? fun s =>
        if s.structDef.name == name then
          some (s.structDef.fields.map fun f =>
            toSnakeCase f.name)
        else none
    let modCtx := { ctx with
      currentModule := modName }
    let items :=
      modStructs.flatMap (·.structDef.toRustItems) ++
      modEnums.map (·.enumDef.toRustItem) ++
      modFns.map
        (·.fnDef.toRustItem structFieldLookup modCtx) ++
      modProps.map (·.propertyDef.fnDef.toRustItem
        structFieldLookup modCtx) ++
      modExtras
    let doc := match modEnums.head? with
      | some e => e.enumDef.doc.toPlainText
      | none => match modStructs.head? with
        | some s => s.structDef.doc.toPlainText
        | none => modName
    let usesHashCollection (t : DSLType) : Bool :=
      match t with
      | .set .. => true | .map .. => true | _ => false
    let usesSet := modFns.any
      fun f => usesHashCollection f.fnDef.returnType
    let usesSetProp := modProps.any
      fun p => usesHashCollection
        p.propertyDef.fnDef.returnType
    let usesMap := modStructs.any fun s =>
      s.structDef.fields.any fun f =>
        match f.ty with | .map .. => true | _ => false
    let extraUses :=
      let needsHashSet := usesSet || usesSetProp
      let needsHashMap := usesMap ||
        modFns.any fun f =>
          match f.fnDef.returnType with
          | .map .. => true | _ => false
      match needsHashSet, needsHashMap with
      | false, false => []
      | true, false => ["std::collections::HashSet"]
      | false, true => ["std::collections::HashMap"]
      | true, true =>
        [ "std::collections::HashSet"
        , "std::collections::HashMap" ]
    { name := ⟨modName⟩, doc := doc, items := items,
      extraUses := extraUses }

namespace OrderDef

/-- The `std::cmp::Ordering` path. -/
private def ordPath (variant : String) : RustPath :=
  ⟨[⟨"std"⟩, ⟨"cmp"⟩, ⟨"Ordering"⟩, ⟨variant⟩]⟩

/-- Classify a pair as Less, Greater, or incomparable. -/
private inductive CmpResult where
  | less | greater | incomparable

/-- Build a merged match arm from pairs sharing a result. -/
private def mergedArm
    (pairs : List (String × String))
    (result : RustExpr)
    : RustMatchArm :=
  let pats := pairs.map fun (a, b) =>
    RustPat.tuple [.selfVariant ⟨a⟩, .selfVariant ⟨b⟩]
  .mk (.or pats) result

/-- Generate a `PartialOrd` impl from this order. -/
def toRustPartialOrd (o : OrderDef) : RustItem :=
  let selfTy := RustTy.self_
  let selfRef := RustTy.refTo selfTy
  let retTy := RustTy.adt ⟨[⟨"Option"⟩]⟩
    [.adt ⟨[⟨"std"⟩, ⟨"cmp"⟩, ⟨"Ordering"⟩]⟩ []]
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
      name := ⟨"partial_cmp"⟩
      params :=
        [ .selfRef
        , .named (.ident ⟨"other"⟩) selfRef ]
      retTy := some retTy
      body := body }
  .impl_ {
    trait_ := some { path := .simple "PartialOrd" }
    ty := ⟨[⟨o.enumName⟩]⟩
    methods := [partialCmpFn] }

end OrderDef
