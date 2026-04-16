import Core.Doc

-- ══════════════════════════════════════════════
-- LaTeX AST
-- ══════════════════════════════════════════════

mutual
  /-- A LaTeX fragment in text mode. -/
  inductive Latex where
    /-- Escaped text (Unicode→LaTeX applied at render). -/
    | text (s : String)
    /-- Raw LaTeX passed through verbatim. -/
    | raw (s : String)
    /-- Concatenation of fragments. -/
    | seq (ls : List Latex)
    /-- Line break in output. -/
    | newline
    /-- `\textbf{...}`. -/
    | textbf (body : Latex)
    /-- `\textit{...}`. -/
    | textit (body : Latex)
    /-- `\texttt{...}`. -/
    | texttt (body : Latex)
    /-- Inline math: `$...$`. -/
    | inlineMath (body : LatexMath)
    /-- Display math: `\[...\]`. -/
    | displayMath (body : LatexMath)
    /-- A command: `\name{arg1}{arg2}...`. -/
    | cmd (name : String) (args : List Latex)
    /-- An environment: `\begin{name}...\end{name}`. -/
    | env (name : String) (body : Latex)
    /-- An environment with options:
        `\begin{name}[opts]...\end{name}`. -/
    | envOpts (name : String) (opts : String)
        (body : Latex)
    deriving Repr, Inhabited

  /-- A LaTeX fragment in math mode. -/
  inductive LatexMath where
    /-- A math variable (escaped at render). -/
    | var (s : String)
    /-- Text that needs math-mode escaping. -/
    | escaped (s : String)
    /-- Raw math LaTeX, verbatim. -/
    | raw (s : String)
    /-- Concatenation. -/
    | seq (ms : List LatexMath)
    /-- `\text{...}` inside math mode. -/
    | text (body : Latex)
    /-- `\texttt{...}` inside math. -/
    | texttt (s : String)
    /-- `\mathbf{...}`. -/
    | mathbf (body : LatexMath)
    /-- `\mathbb{...}`. -/
    | mathbb (body : LatexMath)
    /-- `\mathit{...}`. -/
    | mathit (body : LatexMath)
    /-- `\mathcal{...}`. -/
    | mathcal (body : LatexMath)
    /-- Binary operator: `lhs op rhs`. -/
    | binop (op : String) (lhs : LatexMath)
        (rhs : LatexMath)
    /-- Subscript: `base_{sub}`. -/
    | sub (base : LatexMath) (subscript : LatexMath)
    /-- A nullary math command: `\forall`, etc. -/
    | cmd (name : String)
    /-- Delimited group: `open body close`. -/
    | delimited (open_ : String) (close_ : String)
        (body : LatexMath)
    /-- Array: `\begin{array}[align]{cols}...\end{array}`. -/
    | array (align : Option String) (cols : String)
        (rows : List (List LatexMath))
    deriving Repr, Inhabited
end

-- ══════════════════════════════════════════════
-- Convenience constructors
-- ══════════════════════════════════════════════

namespace Latex

/-- Join fragments with newlines between them. -/
def lines (ls : List Latex) : Latex :=
  .seq (ls.intersperse .newline)

/-- `\cmd` with no arguments. -/
def cmd0 (name : String) : Latex := .cmd name []

/-- `\FloatBarrier` (from the `placeins` package). Flushes
    pending floats so they cannot escape past this point
    into a later (sub)section. -/
def floatBarrier : Latex := cmd0 "FloatBarrier"

/-- `\tableofcontents`. -/
def tableofcontents : Latex := cmd0 "tableofcontents"

/-- `\newpage`. -/
def newpage : Latex := cmd0 "newpage"

/-- `\section{title}`, preceded by a `\FloatBarrier` so that
    any pending floats from the previous section are flushed
    before the new section begins. -/
def «section» (title : Latex) : Latex :=
  .seq [floatBarrier, .newline, .cmd "section" [title]]

/-- `\subsection{title}`, preceded by a `\FloatBarrier` so
    that any pending floats from the previous subsection are
    flushed before the new subsection begins. This ensures
    all content in a subsection appears before the next
    subsection header, even if it results in whitespace. -/
def «subsection» (title : Latex) : Latex :=
  .seq [floatBarrier, .newline, .cmd "subsection" [title]]

/-- `\subsubsection{title}`. -/
def «subsubsection» (title : Latex) : Latex :=
  .cmd "subsubsection" [title]

/-- `\item body`. -/
def item (body : Latex) : Latex := .cmd "item" [body]

/-- `\State body` (algorithmic, space-separated). -/
def state (body : Latex) : Latex :=
  .seq [.raw "\\State ", body]

/-- `\Require body` (algorithmic, space-separated). -/
def require_ (body : Latex) : Latex :=
  .seq [.raw "\\Require ", body]

/-- `\caption{body}`. -/
def caption (body : Latex) : Latex :=
  .cmd "caption" [body]

/-- `\usepackage{name}`. -/
def usepackage (name : String) : Latex :=
  .cmd "usepackage" [.raw name]

/-- Full `\documentclass{article}` document. -/
def document (packages : List String)
    (preamble : Latex) (body : Latex) : Latex :=
  .seq [
    .cmd "documentclass" [.raw "article"], .newline,
    .seq (packages.map fun p =>
      .seq [usepackage p, .newline]),
    preamble, .newline,
    .env "document" (.seq [.newline, body])
  ]

end Latex

namespace LatexMath

/-- Intercalate a separator between math fragments. -/
def intercalate (sep : LatexMath)
    (ms : List LatexMath) : LatexMath :=
  match ms with
  | [] => .seq []
  | [m] => m
  | _ => .seq (ms.intersperse sep)

end LatexMath

-- ══════════════════════════════════════════════
-- Rendering
-- ══════════════════════════════════════════════

mutual
  /-- Render a text-mode LaTeX AST to a string. -/
  partial def Latex.render : Latex → String
    | .text s => Doc.escapeLatex s
    | .raw s => s
    | .seq ls => String.join (ls.map Latex.render)
    | .newline => "\n"
    | .textbf body => s!"\\textbf\{{body.render}}"
    | .textit body => s!"\\textit\{{body.render}}"
    | .texttt body => s!"\\texttt\{{body.render}}"
    | .inlineMath body =>
      s!"${LatexMath.render body}$"
    | .displayMath body =>
      s!"\\[ {LatexMath.render body} \\]"
    | .cmd name args =>
      let argStrs := args.map fun a =>
        s!"\{{a.render}}"
      s!"\\{name}{String.join argStrs}"
    | .env name body =>
      s!"\\begin\{{name}}\n\
         {body.render}\
         \\end\{{name}}"
    | .envOpts name opts body =>
      s!"\\begin\{{name}}[{opts}]\n\
         {body.render}\
         \\end\{{name}}"

  /-- Render a math-mode LaTeX AST to a string. -/
  partial def LatexMath.render : LatexMath → String
    | .var s =>
      let e := Doc.escapeLatexMath s
      if s.length > 1 then s!"\\mathit\{{e}}" else e
    | .escaped s =>
      let e := Doc.escapeLatexMath s
      if s.length > 1 then s!"\\mathit\{{e}}" else e
    | .raw s => s
    | .seq ms =>
      String.join (ms.map LatexMath.render)
    | .text body => s!"\\text\{{Latex.render body}}"
    | .texttt s =>
      s!"\\texttt\{{Doc.escapeLatexCode s}}"
    | .mathbf body =>
      s!"\\mathbf\{{body.render}}"
    | .mathbb body =>
      s!"\\mathbb\{{body.render}}"
    | .mathit body =>
      s!"\\mathit\{{body.render}}"
    | .mathcal body =>
      s!"\\mathcal\{{body.render}}"
    | .binop op lhs rhs =>
      s!"{lhs.render} {op} {rhs.render}"
    | .sub base subscript =>
      s!"{base.render}_\{{subscript.render}}"
    | .cmd name => s!"\\{name}"
    | .delimited open_ close_ body =>
      s!"{open_}{body.render}{close_}"
    | .array align cols rows =>
      let rowStrs := rows.map fun cells =>
        let cellStrs :=
          cells.map LatexMath.render
        s!"  {" &".intercalate cellStrs} \\\\"
      let optStr := match align with
        | some a => s!"[{a}]"
        | none => ""
      s!"\\begin\{array}{optStr}\{{cols}}\n\
         {"\n".intercalate rowStrs}\n\
         \\end\{array}"
end

-- ══════════════════════════════════════════════
-- Doc → Latex / LatexMath conversions
-- ══════════════════════════════════════════════

namespace MathSym

/-- Convert a math symbol to a `LatexMath` AST. -/
def toLatex : MathSym → LatexMath
  | .langle => .cmd "langle"
  | .rangle => .cmd "rangle"
  | .lbracket => .raw "["
  | .rbracket => .raw "]"
  | .lparen => .raw "("
  | .rparen => .raw ")"
  | .lbrace => .raw "\\{"
  | .rbrace => .raw "\\}"
  | .emptySet => .raw "\\emptyset"
  | .setContains => .raw " \\in "
  | .space => .raw "~"
  | .lt => .raw " < "
  | .le => .raw " \\leqslant "
  | .neq => .raw " \\neq "
  | .add => .raw " + "
  | .sub => .raw " - "
  | .mul => .raw " \\cdot "
  | .div => .raw " / "
  | .land => .raw " \\land "
  | .lor => .raw " \\lor "
  | .implies => .raw " \\to "
  | .forall_ => .raw "\\forall "
  | .top => .raw "\\top"
  | .bot => .raw "\\bot"
  | .comma => .raw ",~"
  | .dot => .raw "."
  | .cons => .raw " :: "
  | .underscore => .raw "\\_"
  | .mapsto => .raw " \\mapsto "
  | .cup => .raw " \\cup "
  | .leftarrow => .raw " \\leftarrow "
  | .assign => .raw " := "
  | .append => .raw " \\mathbin{\\texttt{++}} "
  | .pipe => .raw "|"
  | .lambda => .raw "\\lambda "
  | .semicolon => .raw ";"

end MathSym

mutual
  /-- Convert a `Doc` to text-mode `Latex` AST. -/
  partial def Doc.toLatex : Doc → Latex
    | .plain s => .text s
    | .bold d => .textbf d.toLatex
    | .italic d => .textit d.toLatex
    | .code s => .texttt (.raw (Doc.escapeLatexCode s))
    | .seq ds => .seq (ds.map Doc.toLatex)
    | .line => .newline
    | .itemize items =>
      .env "itemize" (.seq (items.map fun d =>
        .seq [Latex.item d.toLatex, .newline]))
    | .raw latex _ _ => .raw latex
    | .link text url =>
      if url.startsWith "#" then
        let target := url.drop 1
        .seq [.raw ("\\hyperlink{" ++ target ++ "}{"),
          text.toLatex, .raw "}"]
      else
        .cmd "href" [.raw (url.replace "#" "\\#"),
          .cmd "textcolor" [.raw "blue",
            .cmd "uline" [text.toLatex]]]
    | .underline .solid body =>
      .cmd "uline" [body.toLatex]
    | .underline .dashed body =>
      .cmd "dashuline" [body.toLatex]
    | .math m => .inlineMath m.toLatexMath

  /-- Convert `MathDoc` to text-mode `Latex` AST. -/
  partial def MathDoc.toLatex : MathDoc → Latex
    | .raw s => .inlineMath (.var s)
    | .doc d => d.toLatex
    | .sym s => .inlineMath s.toLatex
    | .bb d => .inlineMath (.mathbb d.toLatexMath)
    | .bold d => .inlineMath (.mathbf d.toLatexMath)
    | .italic d => .inlineMath (.mathit d.toLatexMath)
    | .cal d => .inlineMath (.mathcal d.toLatexMath)
    | .seq ds => .seq (ds.map MathDoc.toLatex)

  /-- Convert `Doc` to math-mode `LatexMath` AST. -/
  partial def Doc.toLatexMath : Doc → LatexMath
    | .plain s => .text (.text s)
    | .bold d => .mathbf d.toLatexMath
    | .italic d => d.toLatexMath
    | .code s => .texttt s
    | .seq ds => .seq (ds.map Doc.toLatexMath)
    | .line => .raw "\n"
    | .itemize items =>
      .seq (items.map Doc.toLatexMath)
    | .raw latex _ _ => .raw latex
    | .link text url =>
      if url.startsWith "#" then
        let target := url.drop 1
        .text (.seq [.raw ("\\hyperlink{" ++ target ++ "}{"),
          text.toLatex, .raw "}"])
      else
        .text (.cmd "href"
          [.raw (url.replace "#" "\\#"),
           .cmd "textcolor" [.raw "blue",
             .cmd "uline" [text.toLatex]]])
    | .underline .solid body =>
      .text (.cmd "uline" [body.toLatex])
    | .underline .dashed body =>
      .text (.cmd "dashuline" [body.toLatex])
    | .math m => MathDoc.toLatexMath m

  /-- Convert `MathDoc` to math-mode `LatexMath` AST. -/
  partial def MathDoc.toLatexMath : MathDoc → LatexMath
    | .raw s => .escaped s
    | .doc d => d.toLatexMath
    | .sym s => s.toLatex
    | .bb d => .mathbb d.toLatexMath
    | .bold d => .mathbf d.toLatexMath
    | .italic d => .mathit d.toLatexMath
    | .cal d => .mathcal d.toLatexMath
    | .seq ds => .seq (ds.map MathDoc.toLatexMath)
end

namespace Doc

/-- Render a type name to math-mode `LatexMath`. -/
def typeToLatexMathAst (s : String) : LatexMath :=
  let s := s.trimAscii.toString
  match s with
  | "Nat" => .mathbb (.raw "N")
  | "String" => .text (.raw "String")
  | other => .text (.text other)

end Doc
