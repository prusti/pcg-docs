import LSpec
import Core.Dsl.DslType
import Core.Doc
import Core.Export.Latex
import Core.Dsl.LatexParse

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

def main (args : List String) : IO UInt32 :=
  lspecIO
    (.ofList [
      ("DSLType", [dslTypeParseTests]),
      ("Doc", [docLinkTests]),
      ("LatexParse", [latexParseTests])])
    args
