import LSpec
import Core.Dsl.DslType
import Core.Doc
import Core.Doc.Interp
import Core.Export.Latex
import Core.Dsl.Lint
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.PresentationDef
import Core.Dsl.Types.RenderCtx
import Core.Dsl.Types.Feature
import Tests.DslGotoDef
import Tests.ProofFolding

open LSpec DSLType

def dslTypeParseTests : TestSeq :=
  group "DSLType.parse" $
    test "Nat" (parse "Nat" == .prim .nat) $
    test "Option Nat"
      (parse "Option Nat" == .option (.prim .nat)) $
    test "Option (Option UInt8)"
      (parse "Option (Option UInt8)" ==
        .option (.option (.prim .u8))) $
    test "List (Option String)"
      (parse "List (Option String)" ==
        .list (.option (.prim .string))) $
    test "Option (List Bool)"
      (parse "Option (List Bool)" ==
        .option (.list (.prim .bool))) $
    test "UInt64"
      (parse "UInt64" == .prim .u64) $
    test "named type"
      (parse "Place" == .named ⟨"Place"⟩) $
    test "arrow"
      (parse "RegionVid → Location → Bool" ==
        .arrow (.named ⟨"RegionVid"⟩)
          (.arrow (.named ⟨"Location"⟩) (.prim .bool))) $
    test "arrow with paren lhs"
      (parse "(A → B) → C" ==
        .arrow (.arrow (.named ⟨"A"⟩) (.named ⟨"B"⟩))
               (.named ⟨"C"⟩)) $
    .done

private def sampleLink : Doc :=
  .link (.plain "Rust") "https://www.rust-lang.org"

private def styledLink : Doc :=
  .link (.bold (.plain "Click")) "https://example.com"

private def internalLink : Doc :=
  .link (.plain "Value") "#type:Value"

def docLinkTests : TestSeq :=
  group "Doc.link" $
    test "toPlainText renders text (url)"
      (sampleLink.toPlainText ==
        "Rust (https://www.rust-lang.org)") $
    test "toHTML renders <a href=...>"
      (sampleLink.toHTML ==
        "<a href=\"https://www.rust-lang.org\">Rust</a>") $
    test "toTypst renders #link(...)[...]"
      (sampleLink.toTypst ==
        "#link(\"https://www.rust-lang.org\")[Rust]") $
    test "toLatex styles external links with blue \\uline"
      (sampleLink.toLatex.render ==
        "\\href{https://www.rust-lang.org}\
         {\\textcolor{blue}{\\uline{Rust}}}") $
    test "toHTML preserves nested formatting"
      (styledLink.toHTML ==
        "<a href=\"https://example.com\"><b>Click</b></a>") $
    test "toLatex preserves nested formatting"
      (styledLink.toLatex.render ==
        "\\href{https://example.com}\
         {\\textcolor{blue}{\\uline{\\textbf{Click}}}}") $
    test "toLatex styles internal links with \\dashuline"
      (internalLink.toLatex.render ==
        "\\hyperlink{type:Value}{\\dashuline{Value}}") $
    test "MathDoc.seq toTypst preserves child styling"
      ((Doc.math (.seq [.bold (.raw "x"), .raw " + ",
          .italic (.raw "y")])).toTypst ==
        "bold(x) + italic(y)") $
    .done

/-- Build a single-arm `match` whose only arm uses `pat`. The
    scrutinee and rhs are arbitrary leaves so the match-shape
    check is what drives the lint outcome. -/
private def matchWithPat (pat : BodyPat) : DslExpr :=
  .match_ (.var "x") [([pat], .var "y", [])]

def lintTests : TestSeq :=
  group "DslLint" $
    test "wildcard pattern is irrefutable"
      (BodyPat.isIrrefutable .wild == true) $
    test "variable pattern is irrefutable"
      (BodyPat.isIrrefutable (.var "x") == true) $
    test "true/false patterns are refutable (Bool ctors)"
      (BodyPat.isIrrefutable (.var "true") == false &&
         BodyPat.isIrrefutable (.var "false") == false) $
    test "tuple of variables is irrefutable"
      (BodyPat.isIrrefutable
        (.ctor "⟨⟩" [.var "a", .var "b"]) == true) $
    test "named ctor pattern is refutable"
      (BodyPat.isIrrefutable (.ctor "Some" [.var "x"])
        == false) $
    test "list cons pattern is refutable"
      (BodyPat.isIrrefutable (.cons (.var "h") .nil)
        == false) $
    test "tuple containing a refutable pattern is refutable"
      (BodyPat.isIrrefutable
        (.ctor "⟨⟩" [.var "a", .ctor "Some" [.wild]])
        == false) $
    test "match on irrefutable tuple pattern flagged"
      (let diags := DslLint.lintExpr
        (matchWithPat (.ctor "⟨⟩" [.var "a", .var "b"]))
       diags.length == 1 &&
         (diags.head?.map (·.rule)).getD "" ==
           "irrefutableMatch") $
    test "match on refutable ctor pattern not flagged"
      (DslLint.lintExpr
        (matchWithPat (.ctor "Some" [.var "x"]))
        |>.isEmpty) $
    test "match on true/false arms not flagged"
      (let m := DslExpr.match_ (.var "b")
        [([.var "true"], .true_, []),
         ([.var "false"], .false_, [])]
       (DslLint.lintExpr m).isEmpty) $
    test "multi-arm match with one refutable arm not flagged"
      (let m := DslExpr.match_ (.var "x")
        [([.ctor "Some" [.var "y"]], .var "y", []),
         ([.wild], .none_, [])]
       (DslLint.lintExpr m).isEmpty) $
    test "no backticks → not flagged"
      (DslLint.stringHasBacktickPair "plain text" == false) $
    test "single backtick → not flagged"
      (DslLint.stringHasBacktickPair "use `escape" == false) $
    test "closed backtick pair → flagged"
      (DslLint.stringHasBacktickPair "the `body` field"
        == true) $
    test "two backticks far apart → flagged"
      (DslLint.stringHasBacktickPair "open ` close ` ok"
        == true) $
    test "consecutive same-type binders → flagged"
      (DslLint.mergeableBinders
        [(["m'"], some "Machine"), (["m"], some "Machine")]
        == ["Machine"]) $
    test "single binder group → not flagged"
      (DslLint.mergeableBinders
        [(["m'", "m"], some "Machine")]
        |>.isEmpty) $
    test "consecutive different-type binders → not flagged"
      (DslLint.mergeableBinders
        [(["pr"], some "Program"),
         (["m"], some "Machine")]
        |>.isEmpty) $
    test "untyped binder run → not flagged"
      (DslLint.mergeableBinders
        [(["x"], none), (["y"], none)]
        |>.isEmpty) $
    test "forall_ in lintExpr surfaces mergeableBinders"
      (let body := DslExpr.forall_
        [(["m'"], some "Machine"), (["m"], some "Machine")]
        .true_
       (DslLint.lintExpr body).any
        (·.rule == "mergeableBinders")) $
    test "rawMathSymbolToSym maps single-symbol commands to .sym"
      (DslLint.rawMathSymbolToSym "\\pi" == some "pi" &&
       DslLint.rawMathSymbolToSym "\\varphi" == some "varphi" &&
       DslLint.rawMathSymbolToSym "\\phi" == some "phi" &&
       DslLint.rawMathSymbolToSym "\\mu" == some "mu" &&
       DslLint.rawMathSymbolToSym "\\alpha" == some "alpha" &&
       DslLint.rawMathSymbolToSym "\\theta" == some "theta") $
    test "rawMathSymbolToSym tolerates surrounding whitespace"
      (DslLint.rawMathSymbolToSym "\\pi " == some "pi" &&
       DslLint.rawMathSymbolToSym " \\pi" == some "pi" &&
       DslLint.rawMathSymbolToSym " \\pi " == some "pi") $
    test "rawMathSymbolToSym ignores raw strings that aren't a \
          single math symbol"
      (DslLint.rawMathSymbolToSym "\\quad" == none &&
       DslLint.rawMathSymbolToSym "\\State " == none &&
       DslLint.rawMathSymbolToSym "EvalStmtPhase" == none &&
       DslLint.rawMathSymbolToSym "\\bar{\\tau}" == none &&
       DslLint.rawMathSymbolToSym "" == none) $
    .done

private def boldShorthandSimple : Doc :=
  doc! "value $__W__$ here"

private def boldShorthandSpelled : Doc :=
  .seq [.plain "value ", .math (.bold (.raw "W")),
        .plain " here"]

private def boldShorthandMixed : Doc :=
  doc! "before $__n+1__$ then $X$ after"

private def boldShorthandMixedSpelled : Doc :=
  .seq [.plain "before ", .math (.bold (.raw "n+1")),
        .plain " then ", .math (.seq [.raw "X"]),
        .plain " after"]

private def boldShorthandUnclosed : Doc :=
  doc! "open $__abc and no close"

private def boldTextShorthand : Doc :=
  doc! "the __invariant__ holds"

private def boldTextSpelled : Doc :=
  .seq [.plain "the ", .bold (.plain "invariant"),
        .plain " holds"]

private def greekInMathInterp : Doc :=
  doc! "the provenance $π$ identifies an allocation"

private def greekInMathSpelled : Doc :=
  .seq [.plain "the provenance ",
        .math (.seq [.sym .pi]),
        .plain " identifies an allocation"]

def docInterpTests : TestSeq :=
  group "Doc.Interp" $
    test "$__W__$ shorthand renders the same LaTeX as the \
          spelled-out form"
      (boldShorthandSimple.toLatex.render ==
         boldShorthandSpelled.toLatex.render) $
    test "$__n+1__$ accepts non-identifier inner content"
      (boldShorthandMixed.toLatex.render ==
         boldShorthandMixedSpelled.toLatex.render) $
    test "Unmatched $__ falls back to literal characters"
      (boldShorthandUnclosed.toPlainText ==
        "open $__abc and no close") $
    test "__X__ outside $...$ becomes Doc.bold (Doc.plain X)"
      (boldTextShorthand.toLatex.render ==
         boldTextSpelled.toLatex.render) $
    test "Unicode π inside $...$ becomes MathDoc.sym .pi"
      (greekInMathInterp.toLatex.render ==
         greekInMathSpelled.toLatex.render) $
    .done

/-! # Feature-flag tests

A small two-variant enum and a small two-arm function used by
the feature-flag tests below. The first variant / arm carries
`features := [.enumTypes]`; the second is feature-free. Render
both with and without `enumTypes` disabled and assert the
tagged element appears (or doesn't) in the rendered LaTeX. -/

private def mkVariant (n sym : String)
    (feats : List Feature) : VariantDef :=
  VariantDef.mk ⟨n⟩ (Doc.plain n)
    (fun _ => MathDoc.text sym) [] feats

private def gatedEnum : EnumDef :=
  EnumDef.mk ⟨"GatedEnum"⟩ (MathDoc.text "ge")
    (MathDoc.text "GatedEnum") "GatedEnum"
    (Doc.plain "Gated test enum")
    [] false false
    [ mkVariant "hidden" "hiddenSym" [.enumTypes]
    , mkVariant "shown" "shownSym" [] ]

private def disabledCtx : RenderCtx :=
  { isFeatureDisabled := fun f => f == .enumTypes }

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def renderInlineMatch (ctx : RenderCtx) : String :=
  let m : DslExpr := .match_ (.var "x")
    [([.ctor "A" []], .var "alpha", [.enumTypes]),
     ([.ctor "B" []], .var "beta", [])]
  let mathDoc := DslExpr.toDoc "fn" ctx (fun _ => none) false m
  LatexMath.render (MathDoc.toLatexMath mathDoc)

def featureFlagTests : TestSeq :=
  group "Feature flag" $
    test "enum: tagged variant omitted when feature disabled"
      (let rendered := (gatedEnum.formalDefLatex
          (fun _ => false)
          (fun f => f == .enumTypes)).render
       !hasSubstr rendered "hiddenSym" &&
         hasSubstr rendered "shownSym") $
    test "enum: tagged variant present when feature enabled"
      (let rendered := (gatedEnum.formalDefLatex).render
       hasSubstr rendered "hiddenSym" &&
         hasSubstr rendered "shownSym") $
    test "inline match: tagged arm omitted when feature disabled"
      (let rendered := renderInlineMatch disabledCtx
       !hasSubstr rendered "alpha" &&
         hasSubstr rendered "beta") $
    test "inline match: tagged arm present when feature enabled"
      (let rendered := renderInlineMatch {}
       hasSubstr rendered "alpha" &&
         hasSubstr rendered "beta") $
    test "MatchArm accessors round-trip"
      (let arm : MatchArm :=
         ([.var "x"], .var "x", [.enumTypes])
       arm.features == [.enumTypes] && arm.pat.length == 1) $
    test "Presentation default: no features disabled"
      (let p : Presentation :=
         { elems := [], filename := "t" }
       p.disabledFeatures == ([] : List Feature)) $
    .done

def main (args : List String) : IO UInt32 :=
  lspecIO
    (.ofList [
      ("DSLType", [dslTypeParseTests]),
      ("Doc", [docLinkTests]),
      ("DocInterp", [docInterpTests]),
      ("DslLint", [lintTests]),
      ("FeatureFlag", [featureFlagTests])])
    args
