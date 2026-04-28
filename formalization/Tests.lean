import LSpec
import Core.Dsl.DslType
import Core.Doc
import Core.Export.Latex
import Core.Dsl.LatexParse
import Core.Dsl.Lint

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
    .done

/-- Render a `MathDoc` to LaTeX math source for comparison
    against expected output. -/
private def renderMath (m : MathDoc) : String :=
  m.toLatexMath.render

def latexParseTests : TestSeq :=
  group "latex! macro" $
    test "atom"
      (renderMath (latex! "x") == "x") $
    test "subscript with single char"
      (renderMath (latex! "t_D") == "t_{D}") $
    test "subscript with braced group"
      (renderMath (latex! "t_{prev}") ==
        "t_{\\mathit{prev}}") $
    test "plain-text round-trip via Doc"
      ((Doc.math (latex! "t_D")).toPlainText == "t_D") $
    test "whitespace separates atoms"
      (renderMath (latex! "x y") == "xy") $
    test "subscript inside Doc.math renders inline math"
      ((Doc.math (latex! "t_D")).toLatex.render ==
        "$t_{D}$") $
    .done

/-- Build a single-arm `match` whose only arm uses `pat`. The
    scrutinee and rhs are arbitrary leaves so the match-shape
    check is what drives the lint outcome. -/
private def matchWithPat (pat : BodyPat) : DslExpr :=
  .match_ (.var "x") [([pat], .var "y")]

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
        [([.var "true"], .true_), ([.var "false"], .false_)]
       (DslLint.lintExpr m).isEmpty) $
    test "multi-arm match with one refutable arm not flagged"
      (let m := DslExpr.match_ (.var "x")
        [([.ctor "Some" [.var "y"]], .var "y"),
         ([.wild], .none_)]
       (DslLint.lintExpr m).isEmpty) $
    .done

def main (args : List String) : IO UInt32 :=
  lspecIO
    (.ofList [
      ("DSLType", [dslTypeParseTests]),
      ("Doc", [docLinkTests]),
      ("LatexParse", [latexParseTests]),
      ("DslLint", [lintTests])])
    args
