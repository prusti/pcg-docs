import Core.Doc
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.DslType

/-- A pattern in a function body. -/
inductive BodyPat where
  | wild
  | var (name : String)
  | ctor (name : String) (args : List BodyPat)
  /-- Empty list pattern: `[]`. -/
  | nil
  /-- List cons pattern: `h :: t`. -/
  | cons (head : BodyPat) (tail : BodyPat)
  deriving Repr

/-- An expression in the function body DSL. -/
inductive BodyExpr where
  | var (name : String)
  | true_
  | false_
  | emptyList
  | none_
  | some_ (e : BodyExpr)
  /-- Struct constructor. `name` is the struct name
      (empty for anonymous tuples). -/
  | mkStruct (name : String) (args : List BodyExpr)
  | cons (head : BodyExpr) (tail : BodyExpr)
  | append (lhs : BodyExpr) (rhs : BodyExpr)
  | dot (recv : BodyExpr) (method : String)
  | flatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Struct field access: `recv.fieldName`. -/
  | field (recv : BodyExpr) (name : String)
  /-- Fallible list indexing: `list[idx]?`. -/
  | index (list : BodyExpr) (idx : BodyExpr)
  /-- Infallible list indexing: `list[idx]`. -/
  | indexBang (list : BodyExpr) (idx : BodyExpr)
  /-- Function call: `fn(arg₁, arg₂, …)`. -/
  | call (fn : String) (args : List BodyExpr)
  /-- Monadic fold: `list.foldlM fn init`. -/
  | foldlM (fn : String) (init : BodyExpr)
      (list : BodyExpr)
  /-- Less-than comparison: `lhs < rhs`. -/
  | lt (lhs : BodyExpr) (rhs : BodyExpr)
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
  returnType : DSLType
  /-- Names of properties that must hold before calling
      this function. -/
  preconditions : List String := []
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
  | .nil =>
    Syntax.mkApp (mkIdent ``BodyPat.nil) #[]
  | .cons h t =>
    Syntax.mkApp (mkIdent ``BodyPat.cons)
      #[quotePat h, quotePat t]

open Lean in
instance : Quote BodyPat where quote := quotePat

open Lean in
partial def quoteExpr : BodyExpr → TSyntax `term
  | .var n =>
    Syntax.mkApp (mkIdent ``BodyExpr.var) #[quote n]
  | .true_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.true_) #[]
  | .false_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.false_) #[]
  | .emptyList =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptyList) #[]
  | .none_ =>
    Syntax.mkApp (mkIdent ``BodyExpr.none_) #[]
  | .some_ e =>
    Syntax.mkApp (mkIdent ``BodyExpr.some_)
      #[quoteExpr e]
  | .mkStruct name args =>
    Syntax.mkApp (mkIdent ``BodyExpr.mkStruct)
      #[quote name, quote (args.map quoteExpr)]
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
  | .indexBang list idx =>
    Syntax.mkApp (mkIdent ``BodyExpr.indexBang)
      #[quoteExpr list, quoteExpr idx]
  | .call fn args =>
    Syntax.mkApp (mkIdent ``BodyExpr.call)
      #[quote fn, quote (args.map quoteExpr)]
  | .foldlM fn init list =>
    Syntax.mkApp (mkIdent ``BodyExpr.foldlM)
      #[quote fn, quoteExpr init, quoteExpr list]
  | .lt l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.lt)
      #[quoteExpr l, quoteExpr r]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

namespace BodyPat

partial def toRust (enumName : String)
    : BodyPat → String
  | .wild => "_"
  | .var n => n.replace "τ₀" "ty0"
    |>.replace "τ" "ty" |>.replace "π" "pi"
  | .ctor "⟨⟩" args =>
    -- Struct destructure: render children without
    -- enum qualification.
    s!"({", ".intercalate
      (args.map (toRust ""))})"
  | .ctor n args =>
    let capName := String.ofList
      (n.toList.head!.toUpper :: n.toList.tail!)
    let argStr := ", ".intercalate
      (args.map (toRust enumName))
    if enumName.isEmpty then
      -- Inside a struct destructure: bare variant
      if args.isEmpty then capName
      else s!"{capName}({argStr})"
    else if args.isEmpty then
      s!"{enumName}::{capName}"
    else
      s!"{enumName}::{capName}({argStr})"
  | .nil => "[]"
  | .cons h tail =>
    let elemName := if enumName.startsWith "List "
      then enumName.drop 5 |>.toString
      else enumName
    let hStr := h.toRust elemName
    let tailStr := match tail with
      | .var rest =>
        let rv := rest.replace "τ" "ty"
          |>.replace "π" "pi"
        s!", {rv} @ .."
      | .wild => ", .."
      | _ => s!", {tail.toRust elemName} @ .."
    s!"[{hStr}{tailStr}]"

end BodyPat

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
  | .nil => "[]"
  | .cons h t =>
    s!"{h.toLatex ctorDisplay} :: {t.toLatex ctorDisplay}"

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
  | .true_ => "\\text{true}"
  | .false_ => "\\text{false}"
  | .emptyList => "\\emptyset"
  | .none_ => "\\text{None}"
  | .some_ e =>
    e.toLatex fnName varDisplay ctorDisplay
  | .mkStruct _ args =>
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
  | .indexBang list idx =>
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
  | .lt l r =>
    s!"{l.toLatex fnName varDisplay ctorDisplay} \
       < {r.toLatex fnName varDisplay ctorDisplay}"

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

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    .seq [.text s!"{p.name} : ", p.ty.toDoc .normal]
  .seq [ f.symbolDoc, .text "(",
    Doc.intercalate (.text ", ") paramDocs,
    .text ") → ", f.returnType.toDoc .normal ]

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
         {(p.ty.toDoc .normal).toLaTeX}")
  let retTy := (f.returnType.toDoc .normal).toLaTeX
  let bodyLines := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let ctorName := arm.pat.head?.bind fun p =>
        match p with | .ctor n _ => some n | _ => none
      let varDisplay : String → Option String :=
        fun varName =>
          match ctorName with
          | none => none
          | some cn =>
            let variant := variants.find? (·.name.name == cn)
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
  let precondLines := f.preconditions.map fun pn =>
    let args := ", ".intercalate
      (f.params.map fun p => Doc.escapeLatex p.name)
    s!"    \\Require ${Doc.escapeLatexMath pn}\
       ({args})$"
  let allLines := precondLines ++ bodyLines
  s!"\\begin{lb}algorithm{rb}\n\
     \\caption{lb}{Doc.escapeLatex f.name}\
     ({paramSig}) \
     $\\to$ {retTy}{rb}\n\
     \\begin{lb}algorithmic{rb}[1]\n\
     {"\n".intercalate allLines}\n\
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
