import Shared.Doc
import Shared.StructDef
import Shared.EnumDef

/-- A pattern in a function body. -/
inductive BodyPat where
  | wild
  | var (name : String)
  | ctor (name : String) (args : List BodyPat)
  deriving Repr

/-- An expression in the function body DSL. -/
inductive BodyExpr where
  | var (name : String)
  | emptyList
  | none_
  | some_ (e : BodyExpr)
  | mkStruct (args : List BodyExpr)
  | cons (head : BodyExpr) (tail : BodyExpr)
  | append (lhs : BodyExpr) (rhs : BodyExpr)
  | dot (recv : BodyExpr) (method : String)
  | flatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : BodyExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : BodyExpr) (idx : BodyExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : String) (args : List BodyExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : String) (init : BodyExpr)
      (list : BodyExpr)
  deriving Repr

/-- A statement in a do-block. -/
inductive BodyStmt where
  /-- `let name := val`. -/
  | let_ (name : String) (val : BodyExpr)
  /-- `let name ← val` (monadic bind). -/
  | letBind (name : String) (val : BodyExpr)
  deriving Repr

/-- A match arm: patterns → expression. -/
structure BodyArm where
  pat : List BodyPat
  rhs : BodyExpr
  deriving Repr

/-- A function body: either pattern-matching arms or an
    imperative do-block. -/
inductive FnBody where
  /-- Pattern-matching function. -/
  | matchArms (arms : List BodyArm)
  /-- Imperative do-block with let bindings. -/
  | doBlock (stmts : List BodyStmt) (ret : BodyExpr)
  deriving Repr

/-- An exportable function definition. -/
structure FnDef where
  name : String
  symbolDoc : Doc
  doc : String
  params : List FieldDef
  returnType : String
  body : FnBody
  deriving Repr

-- ══════════════════════════════════════════════
-- Quote instances
-- ══════════════════════════════════════════════

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
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyExpr.var) #[quote n]
  | .emptyList =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptyList) #[]
  | .none_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.none_) #[]
  | .some_ e =>
    Syntax.mkApp (mkIdent ``BodyExpr.some_)
      #[quoteExpr e]
  | .mkStruct args =>
    Syntax.mkApp (mkIdent ``BodyExpr.mkStruct)
      #[quote (args.map quoteExpr)]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyExpr.cons)
      #[quoteExpr h, quoteExpr t]
  | .append l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.append)
      #[quoteExpr l, quoteExpr r]
  | .dot recv method =>
    Syntax.mkApp (mkIdent ``BodyExpr.dot)
      #[quoteExpr recv, quote method]
  | .flatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.flatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .field recv name =>
    Syntax.mkApp (mkIdent ``BodyExpr.field)
      #[quoteExpr recv, quote name]
  | .index list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.index)
      #[quoteExpr list, quoteExpr idx]
  | .call fn args =>
    Syntax.mkApp (mkIdent ``BodyExpr.call)
      #[quote fn, quote (args.map quoteExpr)]
  | .foldlM fn init list =>
    Syntax.mkApp (mkIdent ``BodyExpr.foldlM)
      #[quote fn, quoteExpr init, quoteExpr list]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

-- ══════════════════════════════════════════════
-- Lean rendering
-- ══════════════════════════════════════════════

namespace BodyPat

partial def toLean : BodyPat → String
  | .wild => "_"
  | .var n => n
  | .ctor "⟨⟩" args =>
    s!"⟨{", ".intercalate (args.map toLean)}⟩"
  | .ctor n args =>
    if args.isEmpty then s!".{n}"
    else s!".{n} {" ".intercalate (args.map toLean)}"

partial def toRust (enumName : String)
    : BodyPat → String
  | .wild => "_"
  | .var n => n
  | .ctor "⟨⟩" args =>
    s!"({", ".intercalate
      (args.map (toRust enumName))})"
  | .ctor n args =>
    let capName := String.ofList
      (n.toList.head!.toUpper :: n.toList.tail!)
    let argStr := ", ".intercalate
      (args.map (toRust enumName))
    if args.isEmpty then
      s!"{enumName}::{capName}"
    else
      s!"{enumName}::{capName}({argStr})"

end BodyPat

namespace BodyExpr

partial def toLean : BodyExpr → String
  | .var n => n
  | .emptyList => "[]"
  | .none_ => "none"
  | .some_ e => s!"some {e.toLean}"
  | .mkStruct args =>
    s!"⟨{", ".intercalate (args.map toLean)}⟩"
  | .cons h t => s!"{h.toLean} :: {t.toLean}"
  | .append l r => s!"{l.toLean} ++ {r.toLean}"
  | .dot recv method =>
    s!"{recv.toLean}.{method}"
  | .flatMap list param body =>
    s!"{list.toLean}.flatMap fun {param} => \
       {body.toLean}"
  | .field recv name => s!"{recv.toLean}.{name}"
  | .index list idx =>
    s!"{list.toLean}[{idx.toLean}]?"
  | .call fn args =>
    let argStr := ", ".intercalate (args.map toLean)
    s!"{fn} {argStr}"
  | .foldlM fn init list =>
    s!"{list.toLean}.foldlM {fn} {init.toLean}"

end BodyExpr

namespace BodyStmt

def toLean : BodyStmt → String
  | .let_ n v => s!"  let {n} := {v.toLean}"
  | .letBind n v => s!"  let {n} ← {v.toLean}"

end BodyStmt

namespace FnBody

def toLean : FnBody → String
  | .matchArms arms =>
    "\n".intercalate (arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map BodyPat.toLean)
      s!"  | {patStr} => {arm.rhs.toLean}")
  | .doBlock stmts ret =>
    let stmtStrs := stmts.map BodyStmt.toLean
    let all := stmtStrs ++ [s!"  {ret.toLean}"]
    " do\n".intercalate [] ++ "\n".intercalate all

end FnBody

-- ══════════════════════════════════════════════
-- LaTeX rendering
-- ══════════════════════════════════════════════

namespace BodyPat

partial def toLatex
    (ctorDisplay : String → Option String)
    : BodyPat → String
  | .wild => "\\_"
  | .var n => Doc.escapeLatexMath n
  | .ctor "⟨⟩" args =>
    s!"({",~".intercalate
      (args.map (toLatex ctorDisplay))})"
  | .ctor n args =>
    match ctorDisplay n with
    | some display => display
    | none =>
      let argStr := ",~".intercalate
        (args.map (toLatex ctorDisplay))
      if args.isEmpty then
        s!"\\text\{{n}}"
      else s!"\\text\{{n}}({argStr})"

end BodyPat

namespace BodyExpr

partial def toLatex
    (fnName : String)
    (varDisplay : String → Option String :=
      fun _ => none)
    (ctorDisplay : String → Option String :=
      fun _ => none)
    : BodyExpr → String
  | .var n => match varDisplay n with
    | some sym => sym
    | none => Doc.escapeLatexMath n
  | .emptyList => "\\emptyset"
  | .none_ => "\\text{None}"
  | .some_ e =>
    e.toLatex fnName varDisplay ctorDisplay
  | .mkStruct args =>
    let inner := ",~".intercalate
      (args.map (toLatex fnName varDisplay
        ctorDisplay))
    s!"({inner})"
  | .cons h t =>
    let lb := "{"
    let rb := "}"
    s!"\\{lb}{h.toLatex fnName varDisplay
      ctorDisplay}\\{rb} \\cup \
      {t.toLatex fnName varDisplay ctorDisplay}"
  | .append l r =>
    s!"{l.toLatex fnName varDisplay ctorDisplay} \
       \\cup \
       {r.toLatex fnName varDisplay ctorDisplay}"
  | .dot recv method =>
    s!"\\text\{{method}}(\
       {recv.toLatex fnName varDisplay ctorDisplay})"
  | .flatMap list param body =>
    let lb := "{"
    let rb := "}"
    s!"\\bigcup_{lb}{Doc.escapeLatexMath param} \
       \\in {list.toLatex fnName varDisplay
         ctorDisplay}{rb} \
       {body.toLatex fnName varDisplay ctorDisplay}"
  | .field recv name =>
    s!"{recv.toLatex fnName varDisplay
      ctorDisplay}.\\text\{{name}}"
  | .index list idx =>
    s!"{list.toLatex fnName varDisplay
      ctorDisplay}[{idx.toLatex fnName varDisplay
        ctorDisplay}]"
  | .call fn args =>
    let argStr := ",~".intercalate
      (args.map (toLatex fnName varDisplay
        ctorDisplay))
    s!"\\text\{{fn}}({argStr})"
  | .foldlM fn init list =>
    s!"\\text\{{fn}}^*({init.toLatex fnName
      varDisplay ctorDisplay},~\
      {list.toLatex fnName varDisplay ctorDisplay})"

end BodyExpr

namespace BodyStmt

def toLatex (fnName : String)
    (varDisplay ctorDisplay
      : String → Option String) : BodyStmt → String
  | .let_ n v =>
    s!"\\text\{let } {Doc.escapeLatexMath n} := \
       {v.toLatex fnName varDisplay ctorDisplay}"
  | .letBind n v =>
    s!"\\text\{let } {Doc.escapeLatexMath n} \
       \\leftarrow \
       {v.toLatex fnName varDisplay ctorDisplay}"

end BodyStmt

-- ══════════════════════════════════════════════
-- Rust rendering
-- ══════════════════════════════════════════════

namespace BodyExpr

/-- Sanitize a name for Rust (replace Unicode). -/
private def rustName (n : String) : String :=
  n.replace "τ₀" "ty0"
   |>.replace "τ" "ty"
   |>.replace "π" "pi"

partial def toRust (fnName : String)
    : BodyExpr → String
  | .var n => rustName n
  | .emptyList => "vec![]"
  | .none_ => "None"
  | .some_ e => s!"Some({e.toRust fnName})"
  | .mkStruct args =>
    s!"({", ".intercalate (args.map (toRust fnName))})"
  | .cons h t =>
    let lb := "{"
    let rb := "}"
    s!"{lb}\n            let mut r = \
       vec![{h.toRust fnName}.clone()];\n\
       \x20           r.extend({t.toRust fnName});\n\
       \x20           r\n        {rb}"
  | .append l r =>
    let lb := "{"
    let rb := "}"
    s!"{lb}\n            let mut r = \
       {l.toRust fnName};\n\
       \x20           r.extend({r.toRust fnName});\n\
       \x20           r\n        {rb}"
  | .dot recv method =>
    s!"{method}(*{recv.toRust fnName}.clone())"
  | .flatMap list param body =>
    s!"{list.toRust fnName}.iter().flat_map(\
       |{param}| {body.toRust fnName}\
       ).collect::<Vec<_>>()"
  | .field recv name =>
    s!"{recv.toRust fnName}.{name}"
  | .index list idx =>
    s!"{list.toRust fnName}.get(\
       {idx.toRust fnName})"
  | .call fn args =>
    let argStr := ", ".intercalate
      (args.map fun a => s!"&{a.toRust fnName}")
    s!"{fn}({argStr})"
  | .foldlM fn init list =>
    s!"{list.toRust fnName}.iter().try_fold(\
       {init.toRust fnName}, |acc, x| \
       {fn}(&acc, x))"

end BodyExpr

-- ══════════════════════════════════════════════
-- FnDef rendering helpers
-- ══════════════════════════════════════════════

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    Doc.text s!"{p.name} : {p.typeName}"
  .seq [ f.symbolDoc, .text "(",
    Doc.intercalate (.text ", ") paramDocs,
    .text s!") → {f.returnType}" ]

/-- Render the function as a LaTeX algorithm. -/
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
  let bodyLines := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let ctorName := arm.pat.head?.bind fun p =>
        match p with | .ctor n _ => some n | _ => none
      let varDisplay : String → Option String :=
        fun varName =>
          match ctorName with
          | none => none
          | some cn =>
            let variant := variants.find? (·.name == cn)
            match variant with
            | none => none
            | some v => v.display.findSome? fun dp =>
              match dp with
              | .arg n sym =>
                if n == varName then
                  some sym.toLatexMath
                else none
              | _ => none
      let patStr := ",~".intercalate
        (arm.pat.map (BodyPat.toLatex ctorDisplay))
      let rhsStr := arm.rhs.toLatex f.name
        varDisplay ctorDisplay
      s!"    \\State \\textbf{lb}case{rb} \
         ${patStr}$: \\Return ${rhsStr}$"
    | .doBlock stmts ret =>
      let noDisp : String → Option String :=
        fun _ => none
      let stmtLines := stmts.map fun s =>
        s!"    \\State ${s.toLatex f.name
          noDisp ctorDisplay}$"
      let retLine :=
        s!"    \\State \\Return \
           ${ret.toLatex f.name noDisp ctorDisplay}$"
      stmtLines ++ [retLine]
  s!"\\begin{lb}algorithm{rb}\n\
     \\caption{lb}{Doc.escapeLatex f.name}\
     ({paramSig}) \
     $\\to$ {retTy}{rb}\n\
     \\begin{lb}algorithmic{rb}[1]\n\
     {"\n".intercalate bodyLines}\n\
     \\end{lb}algorithmic{rb}\n\
     \\end{lb}algorithm{rb}"

/-- Render for non-LaTeX (Doc-based). -/
def algorithmDoc (f : FnDef) : Doc :=
  let noDisplay : String → Option String :=
    fun _ => none
  let header := Doc.seq
    [ .text f.doc, .text " ", f.shortSig ]
  let cases := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map (BodyPat.toLatex noDisplay))
      let rhsStr := arm.rhs.toLatex f.name
        noDisplay noDisplay
      Doc.text s!"case {patStr}: return {rhsStr}"
    | .doBlock _ _ => [Doc.text "(imperative body)"]
  .seq [header, .line, .itemize cases]

end FnDef
