import Core.Export.Latex
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
  deriving Repr, Inhabited

/-- An expression in the function body DSL. -/
inductive BodyExpr where
  | var (name : String)
  | natLit (n : Nat)
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
  /-- Less-than-or-equal: `lhs ≤ rhs`. -/
  | le (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Chained less-than: `a < b < c < …`. -/
  | ltChain (exprs : List BodyExpr)
  /-- Addition: `lhs + rhs`. -/
  | add (lhs : BodyExpr) (rhs : BodyExpr)
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
  /-- Implication: `lhs → rhs`. -/
  | implies (lhs : BodyExpr) (rhs : BodyExpr)
  /-- Universal quantifier: `∀ x, body`. -/
  | forall_ (param : String) (body : BodyExpr)
  /-- Proof placeholder: `sorry`. Used when calling
      a function with preconditions from another
      function that can supply the proof. -/
  | sorryProof
  /-- Raw Lean proof term, invisible in Rust/LaTeX. -/
  | leanProof (term : String)
  /-- Match expression:
      `match scrutinee with | pats => rhs | …`.
      Each arm is a list of patterns paired with a
      right-hand side. -/
  | match_ (scrutinee : BodyExpr)
      (arms : List (List BodyPat × BodyExpr))
  deriving Repr, Inhabited

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
  /-- Direct expression (no pattern match needed). -/
  | expr (body : BodyExpr)
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
  | .natLit n =>
    Syntax.mkApp (mkIdent ``BodyExpr.natLit) #[quote n]
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
  | .le l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.le)
      #[quoteExpr l, quoteExpr r]
  | .ltChain es =>
    Syntax.mkApp (mkIdent ``BodyExpr.ltChain)
      #[quote (es.map quoteExpr)]
  | .add l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.add)
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
  | .implies l r =>
    Syntax.mkApp (mkIdent ``BodyExpr.implies)
      #[quoteExpr l, quoteExpr r]
  | .forall_ p b =>
    Syntax.mkApp (mkIdent ``BodyExpr.forall_)
      #[quote p, quoteExpr b]
  | .sorryProof =>
    Syntax.mkApp (mkIdent ``BodyExpr.sorryProof) #[]
  | .leanProof t =>
    Syntax.mkApp (mkIdent ``BodyExpr.leanProof) #[quote t]
  | .match_ scrut arms =>
    let qArms := arms.map fun (pats, rhs) =>
      Syntax.mkApp (mkIdent ``Prod.mk)
        #[quote pats, quoteExpr rhs]
    Syntax.mkApp (mkIdent ``BodyExpr.match_)
      #[quoteExpr scrut, quote qArms]

open Lean in
instance : Quote BodyExpr where quote := quoteExpr

-- ══════════════════════════════════════════════
-- LaTeX rendering
-- ══════════════════════════════════════════════

namespace BodyPat

partial def toLatexMath
    (ctorDisplay : String → Option LatexMath)
    : BodyPat → LatexMath
  | .wild => .raw "\\_"
  | .var n => .escaped n
  | .ctor "⟨⟩" args =>
    .delimited "(" ")"
      (LatexMath.intercalate (.raw ",~")
        (args.map (toLatexMath ctorDisplay)))
  | .ctor n args =>
    match ctorDisplay n with
    | some display => display
    | none =>
      let argParts := args.map (toLatexMath ctorDisplay)
      if args.isEmpty then .text (.raw n)
      else .seq [ .text (.raw n), .raw "("
                , LatexMath.intercalate (.raw ",~") argParts
                , .raw ")" ]
  | .nil => .raw "[]"
  | .cons h t =>
    .seq [ h.toLatexMath ctorDisplay
         , .raw " :: "
         , t.toLatexMath ctorDisplay ]

end BodyPat

namespace BodyExpr

partial def toLatexMath
    (fnName : String)
    (varDisplay : String → Option LatexMath :=
      fun _ => none)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (isProperty : Bool := false)
    : BodyExpr → LatexMath :=
  let go := toLatexMath fnName varDisplay ctorDisplay
    isProperty
  fun
  | .var n => match varDisplay n with
    | some sym => sym
    | none => .escaped n
  | .natLit n => .raw (toString n)
  | .true_ =>
    if isProperty then .cmd "top"
    else .text (.raw "true")
  | .false_ =>
    if isProperty then .cmd "bot"
    else .text (.raw "false")
  | .emptyList => .raw "[]"
  | .none_ => .text (.raw "None")
  | .some_ e =>
    .seq [.text (.raw "Some"), .raw "(", go e, .raw ")"]
  | .mkStruct name args =>
    if name != "" && args.length == 1 then
      go args.head!
    else
      .delimited "(" ")"
        (LatexMath.intercalate (.raw ",~")
          (args.map go))
  | .cons h t =>
    -- Flatten cons chains ending in `emptyList` into a
    -- list literal `[e₁, e₂, …]`.
    let rec flatten : BodyExpr → Option (List BodyExpr)
      | .emptyList => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      .seq [ .raw "["
           , LatexMath.intercalate (.raw ",~")
               (elems.map go)
           , .raw "]" ]
    | none => .seq [go h, .raw " :: ", go t]
  | .append l r =>
    .seq [ go l, .raw " \\mathbin{\\texttt{++}} "
         , go r ]
  | .dot recv "length" =>
    .seq [.raw "|", go recv, .raw "|"]
  | .dot recv method =>
    .seq [.text (.raw method), .raw "(", go recv
         , .raw ")"]
  | .flatMap list param body =>
    .seq [ go list, .raw ".\\text{flatMap}("
         , .cmd "lambda", .raw " "
         , .escaped param, .raw ".~", go body
         , .raw ")" ]
  | .field recv name =>
    .seq [go recv, .raw ".", .text (.raw name)]
  | .index list idx =>
    .seq [go list, .raw "[", go idx, .raw "]"]
  | .indexBang list idx =>
    .seq [go list, .raw "[", go idx, .raw "]"]
  | .call fn args =>
    .seq [ .text (.raw fn), .raw "("
         , LatexMath.intercalate (.raw ",~")
             (args.map go)
         , .raw ")" ]
  | .foldlM fn init list =>
    .seq [ .text (.raw fn), .raw "^*(", go init
         , .raw ",~", go list, .raw ")" ]
  | .lt l r => .binop "<" (go l) (go r)
  | .le l r => .binop "\\leqslant" (go l) (go r)
  | .ltChain es =>
    LatexMath.intercalate (.raw " < ") (es.map go)
  | .add l r => .binop "+" (go l) (go r)
  | .setAll set param body =>
    .seq [ .cmd "forall", .raw " "
         , .escaped param, .raw " "
         , .cmd "in", .raw " ", go set
         , .raw ",~", go body ]
  | .emptySet => .cmd "emptyset"
  | .setSingleton e =>
    .delimited "\\{" "\\}" (go e)
  | .setUnion l r =>
    .binop "\\cup" (go l) (go r)
  | .setFlatMap list param body =>
    .seq [ .sub (.cmd "bigcup")
             (.seq [.escaped param, .raw " "
                   , .cmd "in", .raw " ", go list])
         , .raw " ", go body ]
  | .and l r => .binop "\\land" (go l) (go r)
  | .implies l r => .binop "\\to" (go l) (go r)
  | .forall_ p b =>
    .seq [ .cmd "forall", .raw " "
         , .escaped p, .raw ",~", go b ]
  | .sorryProof => .seq []
  | .leanProof _ => .seq []
  | .match_ scrut arms =>
    let noCtor : String → Option LatexMath :=
      fun _ => Option.none
    let rows := arms.map fun (pats, rhs) =>
      let patMath := LatexMath.intercalate (.raw ",~")
        (pats.map (BodyPat.toLatexMath noCtor))
      [go rhs, .seq [ .text (.raw "if~")
                     , patMath ]]
    .seq [ .text (.raw "match~")
         , go scrut
         , .raw ": "
         , .delimited "\\left\\{" "\\right."
             (.array Option.none "ll" rows) ]

end BodyExpr

namespace BodyStmt

def toLatexMath (fnName : String)
    (varDisplay ctorDisplay
      : String → Option LatexMath)
    (isProperty : Bool := false)
    : BodyStmt → LatexMath
  | .let_ n v =>
    .seq [ .text (.raw "let "), .escaped n
         , .raw " := "
         , v.toLatexMath fnName varDisplay
             ctorDisplay isProperty ]
  | .letBind n v =>
    .seq [ .text (.raw "let "), .escaped n
         , .raw " ", .cmd "leftarrow", .raw " "
         , v.toLatexMath fnName varDisplay
             ctorDisplay isProperty ]

end BodyStmt

namespace FnDef

def shortSig (f : FnDef) : Doc :=
  let paramDocs := f.params.map fun p =>
    .seq [.plain s!"{p.name} : ", p.ty.toDoc .normal]
  .seq [ f.symbolDoc, .plain "(",
    Doc.intercalate (.plain ", ") paramDocs,
    .plain ") → ", f.returnType.toDoc .normal ]

/-- Render the function as a LaTeX algorithm. -/
def formalDefLatex
    (f : FnDef)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (variants : List VariantDef := [])
    (isProperty : Bool := false)
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
    | .matchArms arms => arms.map fun arm =>
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
          (BodyPat.toLatexMath ctorDisplay))
      let rhsMath := arm.rhs.toLatexMath f.name
        varDisplay ctorDisplay isProperty
      .seq [ .raw "    "
           , Latex.state (.seq [
               .textbf (.raw "case"), .raw " "
             , .inlineMath patMath
             , .raw ": "
             , .inlineMath rhsMath ]) ]
    | .doBlock stmts ret =>
      let noDisp : String → Option LatexMath :=
        fun _ => none
      let stmtLines := stmts.map fun s =>
        .seq [ .raw "    "
             , Latex.state (.inlineMath
                 (s.toLatexMath f.name noDisp
                    ctorDisplay isProperty)) ]
      let retLine :=
        .seq [ .raw "    "
             , Latex.state (.inlineMath
                 (ret.toLatexMath f.name noDisp
                    ctorDisplay isProperty)) ]
      stmtLines ++ [retLine]
    | .expr (.match_ scrut matchArms) =>
      let noDisp : String → Option LatexMath :=
        fun _ => none
      let goExpr := BodyExpr.toLatexMath f.name
        noDisp ctorDisplay isProperty
      let headerLine : Latex :=
        .seq [ .raw "    "
             , Latex.state (.seq [
                 .textbf (.raw "match"), .raw " "
               , .inlineMath (goExpr scrut)
               , .raw ":" ]) ]
      let armLines := matchArms.map fun (pats, rhs) =>
        let patMath := LatexMath.intercalate
          (.raw ",~")
          (pats.map (BodyPat.toLatexMath noDisp))
        let rhsMath := goExpr rhs
        .seq [ .raw "    "
             , Latex.state (.seq [
                 .raw "\\hskip1.5em "
               , .textbf (.raw "case"), .raw " "
               , .inlineMath patMath
               , .raw ": "
               , .inlineMath rhsMath ]) ]
      headerLine :: armLines
    | .expr body =>
      let noDisp : String → Option LatexMath :=
        fun _ => none
      [.seq [ .raw "    "
            , Latex.state (.inlineMath
                (body.toLatexMath f.name noDisp
                   ctorDisplay isProperty)) ]]
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
  .env "algorithm" (.seq [
    Latex.caption caption, .newline,
    .env "algorithmic"
      (.seq [Latex.lines allLines, .newline]),
    .newline
  ])

/-- Render for non-LaTeX (Doc-based). -/
def algorithmDoc (f : FnDef) : Doc :=
  let noDisplay : String → Option LatexMath :=
    fun _ => none
  let header := Doc.seq
    [ .plain f.doc, .plain " ", f.shortSig ]
  let cases := match f.body with
    | .matchArms arms => arms.map fun arm =>
      let patStr := ", ".intercalate
        (arm.pat.map fun p =>
          (p.toLatexMath noDisplay).render)
      let rhsStr := (arm.rhs.toLatexMath f.name
        noDisplay noDisplay).render
      Doc.plain s!"case {patStr}: return {rhsStr}"
    | .doBlock _ _ => [Doc.plain "(imperative body)"]
    | .expr body =>
      let rhsStr := (body.toLatexMath f.name
        noDisplay noDisplay).render
      [Doc.plain s!"return {rhsStr}"]
  .seq [header, .line, .itemize cases]

end FnDef
