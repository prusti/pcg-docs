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

/-- Join a list of documents with a separator. -/
def intercalate (sep : Doc) : List Doc → Doc
  | [] => seq []
  | [d] => d
  | d :: ds => seq [d, sep, intercalate sep ds]

/-- Translate Unicode symbols to LaTeX commands. -/
def escapeLatex : String → String :=
  let replacements :=
    [ ("∅", "\\emptyset")
    , ("⊥", "\\bot")
    , ("⊤", "\\top")
    , ("→", "\\to")
    , ("←", "\\leftarrow")
    , ("≤", "\\leq")
    , ("≥", "\\geq")
    , ("∈", "\\in")
    , ("∀", "\\forall")
    , ("∃", "\\exists")
    , ("¬", "\\neg")
    , ("∧", "\\land")
    , ("∨", "\\lor")
    ]
  fun s => replacements.foldl (fun acc (from_, to) =>
    acc.replace from_ to) s

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

end Doc
