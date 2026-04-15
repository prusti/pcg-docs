import Core.Export.Latex
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.DslExpr
import Core.Dsl.DslType

/-- A match arm: patterns → expression. -/
structure BodyArm where
  pat : List BodyPat
  rhs : DslExpr
  deriving Repr

/-- A function body: either pattern-matching arms or
    a direct expression. -/
inductive FnBody where
  /-- Pattern-matching function. -/
  | matchArms (arms : List BodyArm)
  /-- Direct expression (no pattern match needed). -/
  | expr (body : DslExpr)
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
  doc : Doc
  params : List FieldDef
  returnType : DSLType
  /-- Preconditions that must hold before calling
      this function. -/
  preconditions : List Precondition := []
  body : FnBody
  deriving Repr

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    .seq [.plain s!"{p.name} : ", p.ty.toDoc .normal]
  .seq [ f.symbolDoc, .plain "(",
    Doc.intercalate (.plain ", ") paramDocs,
    .plain ") → ", f.returnType.toDoc .normal ]

private partial def exprLinesTop
    (fnName : String)
    (ctorDisplay : String → Option LatexMath)
    (isProperty : Bool)
    (knownFns : String → Bool)
    (knownCtors : String → Bool)
    (e : DslExpr) (depth : Nat) : List Latex :=
  let noDisp : String → Option LatexMath := fun _ => none
  let goExpr := DslExpr.toLatexMath fnName
    noDisp ctorDisplay isProperty knownFns knownCtors
  let mkIndent (n : Nat) : LatexMath :=
    .raw (String.join (List.replicate n "\\hskip1.5em "))
  match e with
  | .letIn name val rest =>
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , .escaped name
             , .raw " := "
             , goExpr val ])) ]
    letLine :: exprLinesTop fnName ctorDisplay isProperty
      knownFns knownCtors rest depth
  | .letBindIn name val rest =>
    let letLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "let~")
             , .escaped name
             , .raw " ", .cmd "leftarrow", .raw " "
             , goExpr val ])) ]
    letLine :: exprLinesTop fnName ctorDisplay isProperty
      knownFns knownCtors rest depth
  | .ifThenElse cond t e =>
    let ifLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "if~")
             , goExpr cond
             , .raw "~", .text (.raw "then") ])) ]
    let thenLines := exprLinesTop fnName ctorDisplay
      isProperty knownFns knownCtors t (depth + 1)
    let elseLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "else") ])) ]
    let elseLines := exprLinesTop fnName ctorDisplay
      isProperty knownFns knownCtors e (depth + 1)
    ifLine :: thenLines ++ elseLine :: elseLines
  | .match_ scrut matchArms =>
    let headerLine : Latex :=
      .seq [ .raw "    "
           , Latex.state (.inlineMath (.seq [
               mkIndent depth
             , .text (.raw "match~")
             , goExpr scrut
             , .raw ":" ])) ]
    let armBlocks := matchArms.flatMap
      fun (pats, rhs) =>
        let patMath := LatexMath.intercalate
          (.raw ",~")
          (pats.map
            (BodyPat.toLatexMath noDisp knownCtors))
        let isSimple := match rhs with
          | .letIn .. => false
          | .letBindIn .. => false
          | .match_ .. => false
          | .ifThenElse .. => false
          | _ => true
        if isSimple then
          let caseLine : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     mkIndent (depth + 1)
                   , .text (.raw "case~")
                   , patMath
                   , .raw ": "
                   , goExpr rhs ])) ]
          [caseLine]
        else
          let caseLine : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     mkIndent (depth + 1)
                   , .text (.raw "case~")
                   , patMath
                   , .raw ":" ])) ]
          caseLine :: exprLinesTop fnName ctorDisplay
            isProperty knownFns knownCtors rhs (depth + 2)
    headerLine :: armBlocks
  | e =>
    [.seq [ .raw "    "
          , Latex.state (.inlineMath (.seq [
              mkIndent depth, goExpr e ])) ]]

/-- Render the function as a LaTeX algorithm. -/
def formalDefLatex
    (f : FnDef)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (variants : List VariantDef := [])
    (isProperty : Bool := false)
    (knownFns : String → Bool := fun _ => false)
    (knownCtors : String → Bool := fun _ => false)
    : Latex :=
  let paramParts : List Latex := f.params.map fun p =>
    Latex.seq [.text p.name, .raw " : ",
               (p.ty.toDoc .normal).toLatex]
  let paramSig : Latex :=
    .seq (paramParts.intersperse (.raw ", "))
  let caption : Latex :=
    if isProperty then
      .seq [.raw "Property ", .text f.name,
            .raw "(", paramSig, .raw ")"]
    else
      let retTy := (f.returnType.toDoc .normal).toLatex
      .seq [.text f.name, .raw "(",
            paramSig, .raw ") ",
            .inlineMath (.cmd "to"), .raw " ",
            retTy]
  let bodyLines : List Latex := match f.body with
    | .matchArms arms => arms.flatMap fun arm =>
      let ctorName := arm.pat.head?.bind fun p =>
        match p with | .ctor n _ => some n | _ => none
      let varDisplay : String → Option LatexMath :=
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
                  some (MathDoc.toLatexMath sym)
                else none
              | _ => none
      let patMath := LatexMath.intercalate (.raw ",~")
        (arm.pat.map
          (BodyPat.toLatexMath ctorDisplay knownCtors))
      let goExpr := DslExpr.toLatexMath f.name
        varDisplay ctorDisplay isProperty knownFns
        knownCtors
      let rec rhsLines : DslExpr → List Latex
        | .letBindIn name val rest =>
          .seq [ .raw "    "
               , Latex.state (.inlineMath (.seq [
                   .raw "\\hskip1.5em "
                 , .text (.raw "let~")
                 , .escaped name
                 , .raw " ", .cmd "leftarrow", .raw " "
                 , goExpr val ])) ]
          :: rhsLines rest
        | .letIn name val rest =>
          .seq [ .raw "    "
               , Latex.state (.inlineMath (.seq [
                   .raw "\\hskip1.5em "
                 , .text (.raw "let~")
                 , .escaped name
                 , .raw " := "
                 , goExpr val ])) ]
          :: rhsLines rest
        | .ifThenElse cond t e =>
          let ifLine : Latex := .seq
            [ .raw "    "
            , Latex.state (.inlineMath (.seq [
                .raw "\\hskip1.5em "
              , .text (.raw "if~")
              , goExpr cond
              , .raw "~", .text (.raw "then") ])) ]
          let branchLine (label : String)
              (body : DslExpr) : Latex :=
            .seq [ .raw "    "
                 , Latex.state (.inlineMath (.seq [
                     .raw "\\hskip3em "
                   , .text (.raw label)
                   , goExpr body ])) ]
          let elseHeader : Latex := .seq
            [ .raw "    "
            , Latex.state (.inlineMath (.seq [
                .raw "\\hskip1.5em "
              , .text (.raw "else") ])) ]
          [ ifLine, branchLine "" t, elseHeader
          , branchLine "" e ]
        | e =>
          [.seq [ .raw "    "
                , Latex.state (.inlineMath (.seq [
                    .raw "\\hskip1.5em ", goExpr e ])) ]]
      let isSimple := match arm.rhs with
        | .letBindIn .. => false
        | .letIn .. => false
        | .ifThenElse .. => false
        | .match_ .. => false
        | _ => true
      if isSimple then
        let rhsMath := arm.rhs.toLatexMath f.name
          varDisplay ctorDisplay isProperty knownFns
          knownCtors
        [.seq [ .raw "    "
             , Latex.state (.seq [
                 .textbf (.raw "case"), .raw " "
               , .inlineMath patMath
               , .raw ": "
               , .inlineMath rhsMath ]) ]]
      else
        let caseLine : Latex :=
          .seq [ .raw "    "
               , Latex.state (.seq [
                   .textbf (.raw "case"), .raw " "
                 , .inlineMath patMath
                 , .raw ":" ]) ]
        caseLine :: rhsLines arm.rhs
    | .expr body => exprLinesTop f.name ctorDisplay
        isProperty knownFns knownCtors body 0
  let precondLines : List Latex :=
    f.preconditions.map fun pc =>
      let argsMath := LatexMath.intercalate
        (.raw ", ") (pc.args.map LatexMath.escaped)
      .seq [ .raw "    "
           , Latex.require_ (.inlineMath
               (.seq [.escaped pc.name
                     , .raw "(", argsMath
                     , .raw ")"])) ]
  let allLines := precondLines ++ bodyLines
  let descBlock : List Latex :=
    if f.doc.toPlainText.isEmpty then []
    else [.textit f.doc.toLatex, .newline]
  .env "algorithm" (.seq [
    Latex.caption caption, .newline,
    .raw s!"\\label\{fn:{f.name}}", .newline,
    .seq descBlock,
    .env "algorithmic"
      (.seq [Latex.lines allLines, .newline]),
    .newline
  ])

/-- Render for non-LaTeX (Doc-based). -/
def algorithmDoc (f : FnDef) : Doc :=
  let noDisplay : String → Option LatexMath :=
    fun _ => none
  let header := Doc.seq
    [ f.doc, .plain " ", f.shortSig ]
  let cases := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map fun p =>
          (p.toLatexMath noDisplay).render)
      let rhsStr := (arm.rhs.toLatexMath f.name
        noDisplay noDisplay).render
      Doc.plain s!"case {patStr}: return {rhsStr}"
    | .expr body =>
      let rhsStr := (body.toLatexMath f.name
        noDisplay noDisplay).render
      [Doc.plain s!"return {rhsStr}"]
  .seq [header, .line, .itemize cases]

end FnDef
