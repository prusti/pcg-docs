import Shared.Doc
import Shared.StructDef
import Shared.EnumDef

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

/-- Render a pattern to LaTeX math mode.
    `ctorDisplay` maps constructor names to their
    mathematical LaTeX representation. -/
partial def toLatex
    (ctorDisplay : String → Option String)
    : BodyPat → String
  | .wild => "\\_"
  | .var n => Doc.escapeLatexMath n
  | .ctor n args =>
    match ctorDisplay n with
    | some display => display
    | none =>
      let argStr := String.intercalate ", "
        (args.map (toLatex ctorDisplay))
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

/-- Render an expression to LaTeX math mode.
    `varDisplay` maps variable names to their LaTeX symbol
    (from the matched variant's display template).
    `ctorDisplay` maps constructor names to display form. -/
partial def toLatex
    (fnName : String)
    (varDisplay : String → Option String :=
      fun _ => none)
    (ctorDisplay : String → Option String :=
      fun _ => none)
    : BodyExpr → String
  | .emptyList => "\\emptyset"
  | .var n => match varDisplay n with
    | some sym => sym
    | none => Doc.escapeLatexMath n
  | .dot recv method =>
    let r := recv.toLatex fnName varDisplay ctorDisplay
    s!"\\text{lb}{method}{rb}({r})"
  | .cons head tail =>
    let h := head.toLatex fnName varDisplay ctorDisplay
    let t := tail.toLatex fnName varDisplay ctorDisplay
    s!"\\{lb}{h}\\{rb} \\cup {t}"
  | .append lhs rhs =>
    let l := lhs.toLatex fnName varDisplay ctorDisplay
    let r := rhs.toLatex fnName varDisplay ctorDisplay
    s!"{l} \\cup {r}"
  | .flatMap list param body =>
    let l := list.toLatex fnName varDisplay ctorDisplay
    let b := body.toLatex fnName varDisplay ctorDisplay
    s!"\\bigcup_{lb}{Doc.escapeLatexMath param} \
       \\in {l}{rb} {b}"
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
  let noDisplay : String → Option String := fun _ => none
  let cases := f.body.map fun arm =>
    let patStr := String.intercalate ", "
      (arm.pat.map (BodyPat.toLatex noDisplay))
    let rhsStr := arm.rhs.toLatex f.name noDisplay
      noDisplay
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
    with algorithmic pseudocode.
    `ctorDisplay` maps constructor names to their
    mathematical LaTeX form.
    `variants` provides the display templates for building
    variable-to-symbol mappings from matched patterns. -/
def formalDefLatex
    (f : FnDef)
    (ctorDisplay : String → Option String :=
      fun _ => none)
    (variants : List VariantDef := [])
    : String :=
  let lb := "{"
  let rb := "}"
  let paramSig := ", ".intercalate
    (f.params.map fun p =>
      s!"{Doc.escapeLatex p.name} : \
         {Doc.escapeLatex p.typeName}")
  let retTy := Doc.escapeLatex f.returnType
  let cases := f.body.map fun arm =>
    -- Build varDisplay from the pattern's constructor
    let ctorName := arm.pat.head?.bind fun p =>
      match p with
      | .ctor n _ => some n
      | _ => none
    let varDisplay : String → Option String :=
      fun varName =>
        match ctorName with
        | none => none
        | some cn =>
          let variant := variants.find?
            (·.name == cn)
          match variant with
          | none => none
          | some v =>
            v.display.findSome? fun dp =>
              match dp with
              | .arg n sym =>
                if n == varName then
                  some sym.toLatexMath
                else none
              | _ => none
    let patStr := ", ".intercalate
      (arm.pat.map (BodyPat.toLatex ctorDisplay))
    let rhsStr := arm.rhs.toLatex f.name
      varDisplay ctorDisplay
    s!"    \\State \\textbf{lb}case{rb} \
       ${patStr}$: \\Return ${rhsStr}$"
  s!"\\begin{lb}algorithm{rb}\n\
     \\caption{lb}{Doc.escapeLatex f.name}\
     ({paramSig}) \
     $\\to$ {retTy}{rb}\n\
     \\begin{lb}algorithmic{rb}[1]\n\
     {"\n".intercalate cases}\n\
     \\end{lb}algorithmic{rb}\n\
     \\end{lb}algorithm{rb}"

end FnDef
