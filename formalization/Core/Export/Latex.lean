import Core.Doc
import Core.Dsl.DslType
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.OrderDef
import Core.Dsl.Types.PropertyDef
import Core.Export.Lean

-- ══════════════════════════════════════════════
-- FPrim / FType LaTeX rendering
-- ══════════════════════════════════════════════

namespace FPrim

/-- Render a primitive to LaTeX (text mode). -/
def toLatex : FPrim → String
  | .nat => "$\\mathbb{N}$"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "()"

/-- Render a primitive to LaTeX math mode. -/
def toLatexMath : FPrim → String
  | .nat => "\\mathbb{N}"
  | .string => "\\text{String}"
  | .bool => "\\text{Bool}"
  | .unit => "()"

end FPrim

namespace FType

/-- Render a type to LaTeX (text mode). -/
def toLatex : FType → String
  | .prim p => p.toLatex
  | .named n => Doc.escapeLatex n
  | .option t => s!"Option {t.toLatex}"
  | .list t => s!"List {t.toLatex}"

/-- Render a type to LaTeX math mode. -/
def toLatexMath : FType → String
  | .prim p => p.toLatexMath
  | .named n => Doc.escapeLatexMath n
  | .option t =>
    s!"\\text{lb}Option{rb}~{t.toLatexMath}"
  | .list t =>
    s!"\\text{lb}List{rb}~{t.toLatexMath}"
  where lb := "{" ; rb := "}"

end FType

-- ══════════════════════════════════════════════
-- EnumDef LaTeX rendering
-- ══════════════════════════════════════════════

namespace DisplayPart

/-- Render a display part to LaTeX math mode. -/
def toLatexMath : DisplayPart → String
  | .lit d => d.toLatexMath
  | .arg _ sym => sym.toLatexMath

end DisplayPart

namespace VariantDef

/-- Render the variant's display template to LaTeX math. -/
def displayLatexMath (v : VariantDef) : String :=
  String.join (v.display.map DisplayPart.toLatexMath)

end VariantDef

namespace EnumDef

/-- Render the enum as a LaTeX `definition` environment with
    an aligned `array` using the display templates. -/
def formalDefLatex (d : EnumDef) : String :=
  let lb := "{"
  let rb := "}"
  let sym := d.symbolDoc.toLatexMath
  let rows := d.variants.zipIdx.map fun (v, i) =>
    let sep := if i == 0 then "  " else "\\mid"
    let variant := v.displayLatexMath
    let desc := Doc.escapeLatex v.doc
    s!"  {sep} & {variant} & \
       \\text{lb}({desc}){rb} \\\\"
  let arrayBody := "\n".intercalate rows
  s!"\\begin{lb}definition{rb}[{d.name}]\n\
     {Doc.escapeLatex d.doc}\n\
     \\[ {sym} ::= \\begin{lb}array{rb}[t]\
     {lb}rll{rb}\n\
     {arrayBody}\n\
     \\end{lb}array{rb} \\]\n\
     \\end{lb}definition{rb}"

end EnumDef

-- ══════════════════════════════════════════════
-- StructDef LaTeX rendering
-- ══════════════════════════════════════════════

namespace StructDef

/-- Render the struct as a LaTeX `definition` environment. -/
def formalDefLatex (s : StructDef) : String :=
  let lb := "{"
  let rb := "}"
  let fieldRows := s.fields.map fun f =>
    s!"  {Doc.escapeLatexMath f.name} &: \
       {f.ty.toLatexMath} & \
       \\text{lb}({Doc.escapeLatex f.doc}){rb} \\\\"
  let body := if fieldRows.isEmpty then ""
    else
      s!"\n\\[ \\begin{lb}array{rb}{lb}rll{rb}\n\
         {"\n".intercalate fieldRows}\n\
         \\end{lb}array{rb} \\]\n"
  s!"\\begin{lb}definition{rb}[{s.name}]\n\
     {Doc.escapeLatex s.doc}\
     {body}\
     \\end{lb}definition{rb}"

end StructDef

-- ══════════════════════════════════════════════
-- BodyPat / BodyExpr / FnDef LaTeX rendering
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

-- ══════════════════════════════════════════════
-- FnDef rendering helpers
-- ══════════════════════════════════════════════

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    Doc.text s!"{p.name} : {p.typeName}"
  .seq [ f.symbolDoc, .text "(",
    Doc.intercalate (.text ", ") paramDocs,
    .text s!") → {f.returnType.toLean}" ]

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
         {p.ty.toLatex}")
  let retTy := f.returnType.toLatex
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

-- ══════════════════════════════════════════════
-- OrderDef Hasse diagram
-- ══════════════════════════════════════════════

namespace OrderDef

/-- Look up the plain-text symbol for a variant name. -/
private def lookupSymbol (e : EnumDef) (name : String)
    : String :=
  match e.variants.find? (·.name == name) with
  | some v => v.displayDoc.toPlainText
  | none => name

/-- Look up the LaTeX math-mode symbol for a variant. -/
private def lookupSymbolMath
    (e : EnumDef) (name : String) : String :=
  match e.variants.find? (·.name == name) with
  | some v => v.displayLatexMath
  | none => name

/-- Compute the level (longest path to bottom) of each element. -/
private partial def computeLevels
    (elements : List String) (facts : List OrderFact)
    : List (String × Nat) :=
  let childrenOf (x : String) : List String :=
    facts.filter (·.greater == x) |>.map (·.lesser)
  let rec level (x : String) (visited : List String) : Nat :=
    if visited.contains x then 0
    else
      let children := childrenOf x
      if children.isEmpty then 0
      else 1 + children.foldl
        (fun acc c => max acc (level c (x :: visited))) 0
  elements.map fun e => (e, level e [])

/-- Generate a Hasse diagram as a `Doc`.

    Uses tikz for LaTeX, ASCII art for Typst/HTML. -/
def hasseDiagram (o : OrderDef) (e : EnumDef) : Doc :=
  let levels := computeLevels o.elements o.facts
  let maxLvl := levels.foldl (fun acc (_, l) => max acc l) 0
  let grouped : List (Nat × List String) :=
    (List.range (maxLvl + 1)).map fun l =>
      (l, levels.filter (·.2 == l) |>.map (·.1))
  let lb := "{"
  let rb := "}"
  let tikzNodes := grouped.flatMap fun (lvl, names) =>
    let n := names.length
    (List.range names.length |>.zip names).map fun (i, name) =>
      let sym := lookupSymbolMath e name
      let x : Int := (2 * i : Int) - (n - 1 : Int)
      s!"  \\node ({name}) at ({x}, {lvl}) {lb}${sym}${rb};"
  let tikzEdges := o.facts.map fun f =>
    s!"  \\draw ({f.greater}) -- ({f.lesser});"
  let tikzLines := [
    s!"\\begin{lb}tikzpicture{rb}[every node/.style={lb}minimum size=6mm{rb}]",
    String.intercalate "\n" tikzNodes,
    String.intercalate "\n" tikzEdges,
    s!"\\end{lb}tikzpicture{rb}"
  ]
  let tikz := String.intercalate "\n" tikzLines
  let ascii := grouped.reverse.map fun (_, names) =>
    let syms := names.map (lookupSymbol e)
    String.intercalate "   " syms
  let asciiStr := String.intercalate "\n" ascii
  let edges := o.facts.map fun f =>
    s!"{lookupSymbol e f.greater} > {lookupSymbol e f.lesser}"
  let edgesStr := String.intercalate ", " edges
  let typstStr := s!"{asciiStr}\n({edgesStr})"
  .raw tikz typstStr typstStr

end OrderDef

namespace PropertyDef

/-- Render the property as a LaTeX definition
    environment. -/
def formalDefLatex (p : PropertyDef) : String :=
  let lb := "{"
  let rb := "}"
  let title := Doc.escapeLatex p.fnDef.name
  s!"\\begin{lb}definition{rb}[{title}]\n\
     {p.definition.toLaTeX}\n\
     \\end{lb}definition{rb}"

end PropertyDef
