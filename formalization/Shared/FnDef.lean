import Shared.Doc
import Shared.StructDef

/-- A pattern in a function body match arm. -/
inductive BodyPat where
  /-- Constructor pattern: `.ctor arg₁ arg₂ …`. -/
  | ctor (name : String) (args : List BodyPat)
  /-- Variable binding. -/
  | var (name : String)
  /-- Wildcard `_`. -/
  | wild
  deriving Repr

/-- An expression in a function body. -/
inductive BodyExpr where
  /-- Empty list `[]`. -/
  | emptyList
  /-- Variable reference. -/
  | var (name : String)
  /-- Nullary method call: `recv.method`. -/
  | dot (recv : BodyExpr) (method : String)
  /-- Cons: `head :: tail`. -/
  | cons (head : BodyExpr) (tail : BodyExpr)
  /-- Append: `lhs ++ rhs`. -/
  | append (lhs : BodyExpr) (rhs : BodyExpr)
  /-- FlatMap with lambda: `list.flatMap fun x => body`. -/
  | flatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  deriving Repr

/-- A match arm in a function body. -/
structure BodyArm where
  /-- The pattern. -/
  pat : List BodyPat
  /-- The right-hand side. -/
  rhs : BodyExpr
  deriving Repr

namespace BodyPat

/-- Render a pattern to valid Lean syntax. -/
partial def toLean : BodyPat → String
  | .wild => "_"
  | .var n => n
  | .ctor n args =>
    let argStr := " ".intercalate (args.map toLean)
    if args.isEmpty then s!".{n}"
    else s!".{n} {argStr}"

end BodyPat

namespace BodyExpr

/-- Render an expression to valid Lean syntax. -/
partial def toLean : BodyExpr → String
  | .emptyList => "[]"
  | .var n => n
  | .dot recv method => s!"{recv.toLean}.{method}"
  | .cons head tail =>
    s!"{head.toLean} :: {tail.toLean}"
  | .append lhs rhs =>
    s!"{lhs.toLean} ++ {rhs.toLean}"
  | .flatMap list param body =>
    s!"{list.toLean}.flatMap fun {param} => \
       {body.toLean}"

end BodyExpr

open Lean in
partial def quotePat : BodyPat → TSyntax `term
  | .wild => Syntax.mkApp (mkIdent ``BodyPat.wild) #[]
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyPat.var) #[quote n]
  | .ctor n args =>
    let qArgs := args.map quotePat
    Syntax.mkApp (mkIdent ``BodyPat.ctor)
      #[quote n, quote qArgs]

open Lean in
instance : Quote BodyPat where quote := quotePat

open Lean in
partial def quoteExpr : BodyExpr → TSyntax `term
  | .emptyList =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptyList) #[]
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyExpr.var) #[quote n]
  | .dot recv method =>
    Syntax.mkApp (mkIdent ``BodyExpr.dot)
      #[quoteExpr recv, quote method]
  | .cons head tail =>
    Syntax.mkApp (mkIdent ``BodyExpr.cons)
      #[quoteExpr head, quoteExpr tail]
  | .append lhs rhs =>
    Syntax.mkApp (mkIdent ``BodyExpr.append)
      #[quoteExpr lhs, quoteExpr rhs]
  | .flatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.flatMap)
      #[quoteExpr list, quote param, quoteExpr body]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

/-- An exportable function definition with metadata for
    cross-language code generation and presentation. -/
structure FnDef where
  /-- The function name (e.g. `"regions"`). -/
  name : String
  /-- Formatted symbol for document exports. -/
  symbolDoc : Doc
  /-- Top-level documentation. -/
  doc : String
  /-- Parameter names, types, and docs. -/
  params : List FieldDef
  /-- Return type name (e.g. `"List Region"`). -/
  returnType : String
  /-- The match arms of the function body. -/
  body : List BodyArm
  deriving Repr

namespace BodyPat

/-- Render a pattern to LaTeX math mode. -/
partial def toLatex : BodyPat → String
  | .wild => "\\_"
  | .var n => Doc.escapeLatex n
  | .ctor n args =>
    let argStr := String.intercalate ", "
      (args.map toLatex)
    if args.isEmpty then s!"\\text{lb}{n}{rb}"
    else s!"\\text{lb}{n}{rb}({argStr})"
  where lb := "{" ; rb := "}"

/-- Render a pattern to Rust. -/
partial def toRust (enumName : String)
    : BodyPat → String
  | .wild => "_"
  | .var n => n
  | .ctor n args =>
    let capName := n.toList.head!.toUpper ::
      n.toList.tail!
    let name := String.ofList capName
    let argStr := String.intercalate ", "
      (args.map (toRust enumName))
    if args.isEmpty then
      s!"{enumName}::{name}"
    else
      s!"{enumName}::{name}({argStr})"

end BodyPat

namespace BodyExpr

/-- Render an expression to LaTeX math mode. -/
partial def toLatex (fnName : String)
    : BodyExpr → String
  | .emptyList => "\\emptyset"
  | .var n => Doc.escapeLatex n
  | .dot recv method =>
    s!"\\text{lb}{method}{rb}({recv.toLatex fnName})"
  | .cons head tail =>
    s!"\\{lb}{head.toLatex fnName}\\{rb} \\cup \
       {tail.toLatex fnName}"
  | .append lhs rhs =>
    s!"{lhs.toLatex fnName} \\cup \
       {rhs.toLatex fnName}"
  | .flatMap list param body =>
    s!"\\bigcup_{lb}{Doc.escapeLatex param} \
       \\in {list.toLatex fnName}{rb} \
       {body.toLatex fnName}"
  where lb := "{" ; rb := "}"

/-- Render an expression to Rust. -/
partial def toRust (fnName : String)
    : BodyExpr → String
  | .emptyList => "vec![]"
  | .var n => n
  | .dot recv method =>
    s!"{method}({recv.toRust fnName})"
  | .cons head tail =>
    let h := head.toRust fnName
    let t := tail.toRust fnName
    s!"{lb}\n            let mut r = vec![{h}.clone()];\
       \n            r.extend({t});\n\
       \x20           r\n        {rb}"
  | .append lhs rhs =>
    let l := lhs.toRust fnName
    let r := rhs.toRust fnName
    s!"{lb}\n            let mut r = {l};\n\
       \x20           r.extend({r});\n\
       \x20           r\n        {rb}"
  | .flatMap list param body =>
    let l := list.toRust fnName
    let b := body.toRust fnName
    s!"{l}.iter().flat_map(|{param}| \
       {b}).collect::<Vec<_>>()"
  where lb := "{" ; rb := "}"

end BodyExpr

namespace FnDef

/-- Render the function signature for short definitions. -/
def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    Doc.text s!"{p.name} : {p.typeName}"
  .seq [ f.symbolDoc
       , .text "("
       , Doc.intercalate (.text ", ") paramDocs
       , .text s!") → {f.returnType}" ]

/-- Render the function as a LaTeX algorithm with cases. -/
def algorithmDoc (f : FnDef) : Doc :=
  let header := Doc.seq
    [ .text f.doc, .text " ", f.shortSig ]
  let cases := f.body.map fun arm =>
    let patStr := String.intercalate ", "
      (arm.pat.map BodyPat.toLatex)
    let rhsStr := arm.rhs.toLatex f.name
    Doc.raw
      s!"\\textbf{lb}case{rb} ${patStr}$: \
         return ${rhsStr}$"
      s!"**case** {patStr}: return {rhsStr}"
      s!"<b>case</b> {patStr}: return {rhsStr}"
  .seq [ header, .line
       , .raw "\\begin{itemize}"
           "" "<ul>"
       , .line
       , Doc.intercalate .line
           (cases.map fun c =>
             .seq [.raw "\\item " "- " "<li>", c])
       , .line
       , .raw "\\end{itemize}"
           "" "</ul>" ]
  where lb := "{" ; rb := "}"

/-- Render the function as a LaTeX `algorithm` environment
    with algorithmic pseudocode. -/
def formalDefLatex (f : FnDef) : String :=
  let lb := "{"
  let rb := "}"
  let paramSig := ", ".intercalate
    (f.params.map fun p =>
      s!"{Doc.escapeLatex p.name} : \
         \\text{lb}{Doc.escapeLatex p.typeName}{rb}")
  let retTy := Doc.escapeLatex f.returnType
  let cases := f.body.map fun arm =>
    let patStr := ", ".intercalate
      (arm.pat.map BodyPat.toLatex)
    let rhsStr := arm.rhs.toLatex f.name
    s!"    \\State \\textbf{lb}case{rb} \
       ${patStr}$: \\Return ${rhsStr}$"
  s!"\\begin{lb}algorithm{rb}\n\
     \\caption{lb}{Doc.escapeLatex f.name}\
     ({paramSig}) \
     $\\to$ \\text{lb}{retTy}{rb}{rb}\n\
     \\begin{lb}algorithmic{rb}[1]\n\
     {"\n".intercalate cases}\n\
     \\end{lb}algorithmic{rb}\n\
     \\end{lb}algorithm{rb}"

end FnDef
