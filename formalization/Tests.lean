import LSpec
import Core.Dsl.DslType
import Core.Doc
import Core.Doc.Interp
import Core.Doc.PresInterp
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

/-! # `presBody!` tests

`presBody!` is the markdown-like body builder for
`Presentation.elems`. The tests below pin down the four
non-trivial behaviours: paragraph splitting at blank lines,
`[[Name]]` defRef extraction, `# ` headings, and inline-grammar
parity with `doc!`. -/

/-- Reduce a `PresElement` to a tag string for shape-level
    assertions. The doc-content is rendered to LaTeX so a single
    string captures the structure end-to-end. -/
private def presTag : PresElement → String
  | .doc (Doc.section title) =>
    s!"section({title.toLatex.render})"
  | .doc d => s!"doc({d.toLatex.render})"
  | .defRef n => s!"defRef({n})"

private def presTags (es : List PresElement) : List String :=
  es.map presTag

private def presBodySingleParagraph : List PresElement :=
  presBody! "Just one paragraph of prose."

private def presBodyDefRefSplit : List PresElement :=
  presBody! "Before. [[Place]] After."

private def presBodyTwoParagraphs : List PresElement :=
  presBody! "first paragraph

second paragraph"

private def presBodyHeadingThenProse : List PresElement :=
  presBody! "# A Heading

paragraph body"

private def presBodyDefRefBetweenParagraphs : List PresElement :=
  presBody! "intro prose

[[Place]]

trailing prose"

private def presBodyInlineParityProse : Doc :=
  doc! "code `x` and __bold__ and _italic_ and $π$"

private def presBodyInlineParityDoc :=
  presBody! "code `x` and __bold__ and _italic_ and $π$"

private def presBodyUnclosedBracket : List PresElement :=
  presBody! "literal [[unclosed text"

private def presBodyEmptyBrackets : List PresElement :=
  presBody! "literal [[]] empty"

private def docHoleX : Doc := .plain "X"

private def presBodyHole : List PresElement :=
  presBody! "before {docHoleX} after"

private def presBodySoftLineBreak : List PresElement :=
  presBody! "line one
line two"

private def presBodyDottedRef : List PresElement :=
  presBody! "literal [[Foo.Bar]] dotted"

private def presBodyHeadingMidBody : List PresElement :=
  presBody! "first paragraph
# A Heading
second paragraph"

private def presBodyHeadingNoDefRef : List PresElement :=
  presBody! "# Heading [[NotARef]] tail"

private def presBodyMultipleBlankLines : List PresElement :=
  presBody! "alpha


beta"

private def docInPresFirst (es : List PresElement) : Option Doc :=
  match es with
  | .doc d :: _ => some d
  | _ => none

private def hasOneDoc (es : List PresElement) : Bool :=
  match es with
  | [.doc _] => true
  | _ => false

private def hasTwoDocs (es : List PresElement) : Bool :=
  match es with
  | [.doc _, .doc _] => true
  | _ => false

private def hasSectionThenDoc (es : List PresElement) : Bool :=
  match es with
  | [.doc (Doc.section _), .doc _] => true
  | _ => false

private def isOnlySection (es : List PresElement) : Bool :=
  match es with
  | [.doc (Doc.section _)] => true
  | _ => false

private def hasDocDefRefDoc (es : List PresElement)
    (refName : String) : Bool :=
  match es with
  | [.doc _, .defRef n, .doc _] => n == refName
  | _ => false

private def firstDocLatex (es : List PresElement) : String :=
  match es with
  | .doc d :: _ => d.toLatex.render
  | _ => ""

private def firstDocPlain (es : List PresElement) : String :=
  match es with
  | .doc d :: _ => d.toPlainText
  | _ => ""

def presBodyTests : TestSeq :=
  group "Doc.PresInterp" $
    test "single-paragraph string yields one .doc element"
      (hasOneDoc presBodySingleParagraph) $
    test "[[Name]] mid-line splits prose into 3 elements"
      (presTags presBodyDefRefSplit ==
        ["doc(Before. )", "defRef(Place)", "doc( After.)"]) $
    test "blank line breaks paragraphs"
      (hasTwoDocs presBodyTwoParagraphs) $
    test "# heading line yields a .doc Doc.section"
      (hasSectionThenDoc presBodyHeadingThenProse) $
    test "[[Name]] alone between paragraphs collapses blank \
          lines"
      (hasDocDefRefDoc presBodyDefRefBetweenParagraphs "Place") $
    test "inline grammar matches doc! for code/bold/italic/math"
      (firstDocLatex presBodyInlineParityDoc ==
        presBodyInlineParityProse.toLatex.render) $
    test "unclosed [[ falls back to literal characters"
      (hasSubstr (firstDocPlain presBodyUnclosedBracket)
        "[[unclosed") $
    test "empty [[]] falls back to literal characters"
      (firstDocPlain presBodyEmptyBrackets == "literal [[]] empty") $
    test "{expr} hole splices into surrounding paragraph"
      (hasSubstr (firstDocPlain presBodyHole)
        "before X after") $
    test "single newline collapses to space (soft line break)"
      (firstDocPlain presBodySoftLineBreak ==
        "line one line two") $
    test "dotted [[Foo.Bar]] body falls back to literal"
      (firstDocPlain presBodyDottedRef ==
        "literal [[Foo.Bar]] dotted") $
    test "heading mid-body flushes preceding paragraph"
      (presTags presBodyHeadingMidBody ==
        ["doc(first paragraph)",
         "section(A Heading)",
         "doc(second paragraph)"]) $
    test "[[Name]] inside a heading stays literal"
      (isOnlySection presBodyHeadingNoDefRef &&
        hasSubstr (firstDocPlain presBodyHeadingNoDefRef)
          "[[NotARef]]") $
    test "multiple consecutive blank lines collapse to one break"
      (hasTwoDocs presBodyMultipleBlankLines) $
    .done

/-- A `RenderCtx` that knows about `gatedEnum`'s variants
    (no features disabled). The auto-elide tests start from
    this and override `isFeatureDisabled` for the disabled
    case so resolution stays identical across both. -/
private def gatedRegistry : RenderCtx :=
  { variants := gatedEnum.variants
    resolveVariant := fun n =>
      gatedEnum.variants.find? (·.name.name == n) }

/-- Same registry, with `enumTypes` disabled. -/
private def gatedDisabledCtx : RenderCtx :=
  { gatedRegistry with isFeatureDisabled := fun f => f == .enumTypes }

/-- Render an inline match against `gatedEnum`'s variants
    where neither arm carries an explicit `[feature …]`
    annotation. The first arm's patterns are expected to
    auto-inherit features from `hidden`. -/
private def renderAutoElide
    (ctx : RenderCtx) (pats : BodyPat × BodyPat) : String :=
  let m : DslExpr := .match_ (.var "x")
    [([pats.fst], .var "alpha", []),
     ([pats.snd], .var "beta",  [])]
  let mathDoc := DslExpr.toDoc "fn" ctx (fun _ => none) false m
  LatexMath.render (MathDoc.toLatexMath mathDoc)

private def topLevelPats : BodyPat × BodyPat :=
  (.ctor "hidden" [], .ctor "shown" [])

private def nestedPats : BodyPat × BodyPat :=
  (.ctor "Some" [.ctor "hidden" []],
   .ctor "Some" [.ctor "shown"  []])

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
    test "auto-elide: arm matching gated variant omitted"
      (let rendered := renderAutoElide gatedDisabledCtx topLevelPats
       !hasSubstr rendered "alpha" &&
         hasSubstr rendered "beta") $
    test "auto-elide: nested gated variant omits the arm"
      (let rendered := renderAutoElide gatedDisabledCtx nestedPats
       !hasSubstr rendered "alpha" &&
         hasSubstr rendered "beta") $
    test "auto-elide: no elision when feature is enabled"
      (let rendered := renderAutoElide gatedRegistry topLevelPats
       hasSubstr rendered "alpha" &&
         hasSubstr rendered "beta") $
    .done

def main (args : List String) : IO UInt32 :=
  lspecIO
    (.ofList [
      ("DSLType", [dslTypeParseTests]),
      ("Doc", [docLinkTests]),
      ("DocInterp", [docInterpTests]),
      ("PresInterp", [presBodyTests]),
      ("DslLint", [lintTests]),
      ("FeatureFlag", [featureFlagTests])])
    args
