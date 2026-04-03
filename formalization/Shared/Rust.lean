import Shared.RustSyntax
import Shared.EnumDef

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
    | d, .expr e => s!"{renderExpr d e};"
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

/-- Render a top-level Rust item. -/
def render : RustItem → String
  | .enum doc attrs vis name variants =>
    let attrLines := attrs.map (·.render ++ "\n")
    let variantLines := variants.map fun v =>
      s!"{ind 1}/// {v.doc}\n{ind 1}{v.name},"
    s!"/// {doc}\n\
       {String.join attrLines}\
       {vis.render}enum {name} \{\n\
       {String.intercalate "\n" variantLines}\n\
       }"
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

/-- Render a module to a complete Rust source file. -/
def render (m : RustModule) : String :=
  let header := s!"//! {m.doc}\n"
  let body := m.items.map RustItem.render
  s!"{header}\n{String.intercalate "\n\n" body}\n"

/-- Render the `mod` declaration for `lib.rs`. -/
def modDecl (m : RustModule) : String :=
  s!"pub mod {m.name};"

end RustModule

namespace RustCrate

/-- Render the `Cargo.toml` for this crate. -/
def cargoToml (c : RustCrate) : String :=
  let lines := [
    "[package]",
    s!"name = \"{c.name}\"",
    s!"version = \"{c.version}\"",
    s!"edition = \"{c.edition}\"",
    s!"description = \"{c.description}\""
  ]
  String.intercalate "\n" lines ++ "\n"

/-- Render `lib.rs` with module declarations. -/
def libRs (c : RustCrate) : String :=
  let mods := c.modules.map (·.modDecl)
  String.intercalate "\n" mods ++ "\n"

/-- All files in the crate as `(relative_path, contents)` pairs. -/
def files (c : RustCrate) : List (String × String) :=
  let cargoFile := ("Cargo.toml", c.cargoToml)
  let libFile := ("src/lib.rs", c.libRs)
  let modFiles := c.modules.map fun m =>
    (s!"src/{m.name}.rs", m.render)
  cargoFile :: libFile :: modFiles

end RustCrate

namespace EnumDef

/-- Standard derives for a simple Rust enum. -/
private def defaultDerives : List String :=
  ["Debug", "Clone", "Copy", "PartialEq", "Eq", "Hash"]

/-- Convert an `EnumDef` to a `RustItem.enum`. -/
def toRustItem (d : EnumDef) : RustItem :=
  .enum d.doc [.derive defaultDerives] .pub d.name
    (d.variants.map fun v =>
      { doc := v.doc, name := capitalise v.name })

/-- Generate Rust source code for this enum. -/
def toRust (d : EnumDef) : String :=
  d.toRustItem.render

end EnumDef
