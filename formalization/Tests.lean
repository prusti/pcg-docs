import LSpec
import Core.Dsl.DslType
import Core.Doc
import Core.Export.Latex

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
    .done

private def sampleLink : Doc :=
  .link (.plain "Rust") "https://www.rust-lang.org"

private def styledLink : Doc :=
  .link (.bold (.plain "Click")) "https://example.com"

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
    test "toLatex renders \\href{...}{...}"
      (sampleLink.toLatex.render ==
        "\\href{https://www.rust-lang.org}{Rust}") $
    test "toHTML preserves nested formatting"
      (styledLink.toHTML ==
        "<a href=\"https://example.com\"><b>Click</b></a>") $
    test "toLatex preserves nested formatting"
      (styledLink.toLatex.render ==
        "\\href{https://example.com}{\\textbf{Click}}") $
    .done

def main (args : List String) : IO UInt32 :=
  lspecIO
    (.ofList [
      ("DSLType", [dslTypeParseTests]),
      ("Doc", [docLinkTests])])
    args
