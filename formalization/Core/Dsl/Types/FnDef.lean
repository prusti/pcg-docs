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
  /-- Universal quantifier over a set:
      `∀ x ∈ s, body`. -/
  | setAll (set : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Empty set: `∅`. -/
  | emptySet
  /-- Set singleton: `{elem}`. -/
  | setSingleton (elem : BodyExpr)
  /-- Set union: `lhs ∪ rhs`. -/
  | setUnion (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Set flat-map: `⋃_{param ∈ list} body`. -/
  | setFlatMap (list : BodyExpr) (param : String)
      (body : BodyExpr)
  /-- Logical conjunction: `lhs ∧ rhs`. -/
  | and (lhs : BodyExpr) (rhs : BodyExpr)
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

/-- A precondition applied to specific arguments. -/
structure Precondition where
  /-- The property name. -/
  name : String
  /-- The argument names to apply the property to. -/
  args : List String
  deriving Repr

/-- An exportable function definition. -/
structure FnDef where
  name : String
  symbolDoc : Doc
  doc : String
  params : List FieldDef
  returnType : DSLType
  /-- Preconditions that must hold before calling
      this function. -/
  preconditions : List Precondition := []
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
  | .setAll set param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.setAll)
      #[quoteExpr set, quote param, quoteExpr body]
  | .emptySet =>
    Syntax.mkApp (mkIdent ``BodyExpr.emptySet) #[]
  | .setSingleton e =>
    Syntax.mkApp (mkIdent ``BodyExpr.setSingleton)
      #[quoteExpr e]
  | .setUnion l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.setUnion)
      #[quoteExpr l, quoteExpr r]
  | .setFlatMap list param body =>
    Syntax.mkApp (mkIdent ``BodyExpr.setFlatMap)
      #[quoteExpr list, quote param, quoteExpr body]
  | .and l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.and)
      #[quoteExpr l, quoteExpr r]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

namespace BodyPat

partial def toRust (enumName : String)
    (structFields : String → Option (List String)
      := fun _ => none)
    : BodyPat → String
  | .wild => "_"
  | .var n => n.replace "τ₀" "ty0"
    |>.replace "τ" "ty" |>.replace "π" "pi"
  | .ctor "⟨⟩" args =>
    match structFields enumName with
    | some fields =>
      let bindings := fields.zip
        (args.map (toRust "" structFields))
      let inner := ", ".intercalate
        (bindings.map fun (f, v) => s!"{f}: {v}")
      s!"{enumName} \{ {inner} }"
    | none =>
      s!"({", ".intercalate
        (args.map (toRust "" structFields))})"
  | .ctor n args =>
    let capName := String.ofList
      (n.toList.head!.toUpper :: n.toList.tail!)
    let argStr := ", ".intercalate
      (args.map (toRust enumName structFields))
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
    let hStr := h.toRust elemName structFields
    let tailStr := match tail with
      | .var rest =>
        let rv := rest.replace "τ" "ty"
          |>.replace "π" "pi"
        s!", {rv} @ .."
      | .wild => ", .."
      | _ => s!", {tail.toRust elemName structFields} @ .."
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
    (isProperty : Bool := false)
    : BodyExpr → String :=
  let go := toLatex fnName varDisplay ctorDisplay
    isProperty
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none => Doc.escapeLatexMath n
  | .true_ =>
    if isProperty then "\\top" else "\\text{true}"
  | .false_ =>
    if isProperty then "\\bot" else "\\text{false}"
  | .emptyList => "[]"
  | .none_ => "\\text{None}"
  | .some_ e => go e
  | .mkStruct _ args =>
    s!"({",~".intercalate (args.map go)})"
  | .cons h t => s!"{go h} :: {go t}"
  | .append l r =>
    s!"{go l} \\mathbin\{\\texttt\{++}} {go r}"
  | .dot recv method =>
    s!"\\text\{{method}}({go recv})"
  | .flatMap list param body =>
    s!"{go list}.\\text\{flatMap}(\\lambda \
       {Doc.escapeLatexMath param}.~{go body})"
  | .field recv name =>
    s!"{go recv}.\\text\{{name}}"
  | .index list idx =>
    s!"{go list}[{go idx}]"
  | .indexBang list idx =>
    s!"{go list}[{go idx}]"
  | .call fn args =>
    s!"\\text\{{fn}}({",~".intercalate (args.map go)})"
  | .foldlM fn init list =>
    s!"\\text\{{fn}}^*({go init},~{go list})"
  | .lt l r => s!"{go l} < {go r}"
  | .setAll set param body =>
    s!"\\forall {Doc.escapeLatexMath param} \
       \\in {go set},~{go body}"
  | .emptySet => "\\emptyset"
  | .setSingleton e =>
    let lb := "{"
    let rb := "}"
    s!"\\{lb}{go e}\\{rb}"
  | .setUnion l r => s!"{go l} \\cup {go r}"
  | .setFlatMap list param body =>
    let lb := "{"
    let rb := "}"
    s!"\\bigcup_{lb}{Doc.escapeLatexMath param} \
       \\in {go list}{rb} {go body}"
  | .and l r => s!"{go l} \\land {go r}"

end BodyExpr

namespace BodyStmt

def toLatex (fnName : String)
    (varDisplay ctorDisplay
      : String → Option String)
    (isProperty : Bool := false)
    : BodyStmt → String
  | .let_ n v =>
    s!"\\text\{let } {Doc.escapeLatexMath n} := \
       {v.toLatex fnName varDisplay ctorDisplay
         isProperty}"
  | .letBind n v =>
    s!"\\text\{let } {Doc.escapeLatexMath n} \
       \\leftarrow \
       {v.toLatex fnName varDisplay ctorDisplay
         isProperty}"

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
    (isProperty : Bool := false)
    : String :=
  let lb := "{"
  let rb := "}"
  let paramSig := ", ".intercalate
    (f.params.map fun p =>
      s!"{Doc.escapeLatex p.name} : \
         {(p.ty.toDoc .normal).toLaTeX}")
  let caption :=
    if isProperty then
      s!"Property {Doc.escapeLatex f.name}\
         ({paramSig})"
    else
      let retTy := (f.returnType.toDoc .normal).toLaTeX
      s!"{Doc.escapeLatex f.name}\
         ({paramSig}) $\\to$ {retTy}"
  let bodyLines := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let ctorName := arm.pat.head?.bind fun p =>
        match p with | .ctor n _ => some n | _ => none
      let varDisplay : String → Option String :=
        fun varName =>
          match ctorName with
          | none => none
          | some cn =>
            let variant := variants.find?
              (·.name.name == cn)
            match variant with
            | none => none
            | some v => v.display.findSome? fun dp =>
              match dp with
              | .arg n sym =>
                if n == varName then
                  some (Doc.mathToLatexMath sym)
                else none
              | _ => none
      let patStr := ",~".intercalate
        (arm.pat.map (BodyPat.toLatex ctorDisplay))
      let rhsStr := arm.rhs.toLatex f.name
        varDisplay ctorDisplay isProperty
      s!"    \\State \\textbf{lb}case{rb} \
         ${patStr}$: ${rhsStr}$"
    | .doBlock stmts ret =>
      let noDisp : String → Option String :=
        fun _ => none
      let stmtLines := stmts.map fun s =>
        s!"    \\State ${s.toLatex f.name
          noDisp ctorDisplay isProperty}$"
      let retLine :=
        s!"    \\State \
           ${ret.toLatex f.name noDisp ctorDisplay
             isProperty}$"
      stmtLines ++ [retLine]
  let precondLines := f.preconditions.map fun pc =>
    let args := ", ".intercalate
      (pc.args.map Doc.escapeLatex)
    s!"    \\Require ${Doc.escapeLatexMath pc.name}\
       ({args})$"
  let allLines := precondLines ++ bodyLines
  s!"\\begin{lb}algorithm{rb}\n\
     \\caption{lb}{caption}{rb}\n\
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
