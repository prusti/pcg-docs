/-- A backend-agnostic document fragment.

    Represents styled text that can be rendered to LaTeX, Typst,
    HTML, or other backends. -/
inductive Doc where
  /-- Plain text. -/
  | text (s : String)
  /-- Bold content. -/
  | bold (d : Doc)
  /-- Italic content. -/
  | italic (d : Doc)
  /-- Inline code / monospace. -/
  | code (s : String)
  /-- Concatenation of fragments. -/
  | seq (ds : List Doc)
  /-- Line break. -/
  | line
  /-- A bulleted list. -/
  | itemize (items : List Doc)
  /-- Backend-specific raw content. Each backend picks its own
      string; backends without a match render the fallback. -/
  | raw (latex : String) (typst : String) (html : String)
  deriving Repr

namespace Doc

/-- Extract the plain text content, stripping all formatting. -/
partial def toPlainText : Doc → String
  | text s => s
  | bold d => d.toPlainText
  | italic d => d.toPlainText
  | code s => s
  | seq ds => String.join (ds.map toPlainText)
  | line => "\n"
  | itemize items =>
    String.join (items.map fun d => s!"- {d.toPlainText}\n")
  | raw _ _ _ => ""

/-- Join a list of documents with a separator. -/
def intercalate (sep : Doc) : List Doc → Doc
  | [] => seq []
  | [d] => d
  | d :: ds => seq [d, sep, intercalate sep ds]

/-- Unicode-to-LaTeX replacement pairs. Each pair is
    `(unicode, textMode, mathMode)`. -/
private def latexReplacements :
    List (String × String × String) :=
  [ ("`", "'", "'")
  , (" ", " ", "~")
  , ("&", "\\&", "\\&")
  , ("ℕ", "$\\mathbb{N}$", "\\mathbb{N}")
  , ("∅", "$\\emptyset$", "\\emptyset")
  , ("⊥", "$\\bot$", "\\bot")
  , ("⊤", "$\\top$", "\\top")
  , ("→", "$\\to$", "\\to")
  , ("←", "$\\leftarrow$", "\\leftarrow")
  , ("≤", "$\\leq$", "\\leq")
  , ("≥", "$\\geq$", "\\geq")
  , ("∈", "$\\in$", "\\in")
  , ("∀", "$\\forall$", "\\forall")
  , ("∃", "$\\exists$", "\\exists")
  , ("¬", "$\\neg$", "\\neg")
  , ("∧", "$\\land$", "\\land")
  , ("∨", "$\\lor$", "\\lor")
  , ("τ̄", "$\\bar{\\tau}$", "\\bar{\\tau}")
  , ("τ", "$\\tau$", "\\tau")
  , ("π", "$\\pi$", "\\pi")
  , ("⟨", "$\\langle$", "\\langle")
  , ("⟩", "$\\rangle$", "\\rangle")
  ]

/-- Translate Unicode symbols to LaTeX commands (text mode). -/
def escapeLatex : String → String :=
  fun s => latexReplacements.foldl
    (fun acc (from_, to, _) => acc.replace from_ to) s

/-- Translate Unicode symbols to LaTeX commands (math mode,
    no `$...$` wrappers). -/
def escapeLatexMath : String → String :=
  fun s => latexReplacements.foldl
    (fun acc (from_, _, toMath) =>
      acc.replace from_ toMath) s

/-- Render a document to LaTeX. -/
partial def toLaTeX : Doc → String
  | text s => escapeLatex s
  | bold d => s!"\\textbf\{{d.toLaTeX}}"
  | italic d => s!"\\textit\{{d.toLaTeX}}"
  | code s => s!"\\texttt\{{s}}"
  | seq ds => String.join (ds.map toLaTeX)
  | line => "\n"
  | itemize items =>
    let body := items.map fun d =>
      s!"  \\item {d.toLaTeX}"
    s!"\\begin\{itemize}\n\
       {String.intercalate "\n" body}\n\
       \\end\{itemize}"
  | raw latex _ _ => latex

/-- Render a document to LaTeX math mode (no `$` wrappers,
    `\textit` instead of `\textit`, etc). -/
partial def toLatexMath : Doc → String
  | text s => escapeLatexMath s
  | bold d => s!"\\mathbf\{{d.toLatexMath}}"
  | italic d => d.toLatexMath
  | code s => s!"\\texttt\{{s}}"
  | seq ds => String.join (ds.map toLatexMath)
  | line => "\n"
  | itemize items =>
    String.join (items.map toLatexMath)
  | raw latex _ _ => latex

/-- Render a Lean type name to LaTeX math mode. -/
def typeToLatexMath (s : String) : String :=
  let s := s.trim
  match s with
  | "Nat" => "\\mathbb{N}"
  | "String" => "\\text{String}"
  | other =>
    "\\text{" ++ escapeLatexMath other ++ "}"

/-- Render a document to Typst. -/
partial def toTypst : Doc → String
  | text s => s
  | bold d => s!"*{d.toTypst}*"
  | italic d => s!"_{d.toTypst}_"
  | code s => s!"`{s}`"
  | seq ds => String.join (ds.map toTypst)
  | line => "\n"
  | itemize items =>
    let body := items.map fun d =>
      s!"- {d.toTypst}"
    String.intercalate "\n" body
  | raw _ typst _ => typst

/-- Render a document to HTML. -/
partial def toHTML : Doc → String
  | text s => s
  | bold d => s!"<b>{d.toHTML}</b>"
  | italic d => s!"<i>{d.toHTML}</i>"
  | code s => s!"<code>{s}</code>"
  | seq ds => String.join (ds.map toHTML)
  | line => "<br>\n"
  | itemize items =>
    let body := items.map fun d =>
      s!"<li>{d.toHTML}</li>"
    s!"<ul>\n{String.intercalate "\n" body}\n</ul>"
  | raw _ _ html => html

/-- Wrap LaTeX body in a minimal standalone document. -/
def toStandaloneLatex (d : Doc) (packages : List String := [])
    : String :=
  let pkgLines := packages.map fun p =>
    s!"\\usepackage\{{p}}"
  let preamble := String.intercalate "\n" pkgLines
  let body := d.toLaTeX
  let lb := "{"
  let rb := "}"
  s!"\\documentclass{lb}article{rb}\n\
     {preamble}\n\
     \\begin{lb}document{rb}\n\n\
     {body}\n\n\
     \\end{lb}document{rb}\n"

end Doc
