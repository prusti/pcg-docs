/-- A mathematical symbol. -/
inductive MathSym where
  /-- Left angle bracket: ⟨ -/
  | langle
  /-- Right angle bracket: ⟩ -/
  | rangle
  /-- Left bracket: [ -/
  | lbracket
  /-- Right bracket: ] -/
  | rbracket
  /-- Left parenthesis: ( -/
  | lparen
  /-- Right parenthesis: ) -/
  | rparen
  deriving Repr

mutual
  /-- A mathematical document fragment, for content that
      appears in math mode (e.g. inside `\[ ... \]`). -/
  inductive MathDoc where
    /-- A math variable, rendered italic in math mode. -/
    | var (s : String)
    /-- A `Doc` rendered in math context (`.plain` becomes
        `\text{}`, `.code` becomes `\mathtt{}`, etc). -/
    | doc (d : Doc)
    /-- A math symbol. -/
    | sym (s : MathSym)
    /-- Concatenation of mathematical documents. -/
    | seq (ds : List MathDoc)
    deriving Repr

  /-- A backend-agnostic document fragment.

      Represents styled text that can be rendered to LaTeX, Typst,
      HTML, or other backends. -/
  inductive Doc where
    /-- Plain text. -/
    | plain (s : String)
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
    /-- Mathematical content. -/
    | math (m : MathDoc)
    deriving Repr
end

namespace MathSym

/-- Render to LaTeX math mode. -/
def toLatexMath : MathSym → String
  | .langle => "\\langle"
  | .rangle => "\\rangle"
  | .lbracket => "["
  | .rbracket => "]"
  | .lparen => "("
  | .rparen => ")"

/-- Render to plain text. -/
def toPlainText : MathSym → String
  | .langle => "⟨"
  | .rangle => "⟩"
  | .lbracket => "["
  | .rbracket => "]"
  | .lparen => "("
  | .rparen => ")"

end MathSym

namespace Doc

def brackets (d: MathDoc) : MathDoc :=
  .seq [.sym .lbracket, d, .sym .rbracket]



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
  , ("₀", "$_0$", "_0")
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

/-- Join a list of documents with a separator. -/
def intercalate (sep : Doc) : List Doc → Doc
  | [] => seq []
  | [d] => d
  | d :: ds => seq [d, sep, intercalate sep ds]

mutual
  /-- Extract the plain text content, stripping all
      formatting. -/
  partial def toPlainText : Doc → String
    | plain s => s
    | bold d => d.toPlainText
    | italic d => d.toPlainText
    | code s => s
    | seq ds => String.join (ds.map toPlainText)
    | line => "\n"
    | itemize items =>
      String.join
        (items.map fun d => s!"- {d.toPlainText}\n")
    | raw _ _ _ => ""
    | math m => mathToPlainText m

  /-- Extract plain text from a math fragment. -/
  partial def mathToPlainText : MathDoc → String
    | .var s => s
    | .doc d => d.toPlainText
    | .sym s => s.toPlainText
    | .seq ds => String.join (ds.map mathToPlainText)
end

mutual
  /-- Render a document to LaTeX. -/
  partial def toLaTeX : Doc → String
    | plain s => escapeLatex s
    | bold d => s!"\\textbf\{{d.toLaTeX}}"
    | italic d => s!"\\textit\{{d.toLaTeX}}"
    | code s => s!"\\texttt\{{escapeLatex s}}"
    | seq ds => String.join (ds.map toLaTeX)
    | line => "\n"
    | itemize items =>
      let body := items.map fun d =>
        s!"  \\item {d.toLaTeX}"
      s!"\\begin\{itemize}\n\
         {String.intercalate "\n" body}\n\
         \\end\{itemize}"
    | raw latex _ _ => latex
    | math m => mathToLaTeX m

  /-- Render a math fragment to LaTeX (text mode context).
      Variables enter math mode; doc content renders
      normally. -/
  partial def mathToLaTeX : MathDoc → String
    | .var s => s!"${escapeLatexMath s}$"
    | .doc d => d.toLaTeX
    | .sym s => s!"${s.toLatexMath}$"
    | .seq ds => String.join (ds.map mathToLaTeX)
end

mutual
  /-- Render a document to LaTeX math mode. In math mode,
      `.plain` wraps in `\text{}` for correct rendering of
      words. -/
  partial def toLatexMath : Doc → String
    | plain s => s!"\\text\{{escapeLatex s}}"
    | bold d => s!"\\mathbf\{{d.toLatexMath}}"
    | italic d => d.toLatexMath
    | code s => s!"\\texttt\{{escapeLatex s}}"
    | seq ds => String.join (ds.map toLatexMath)
    | line => "\n"
    | itemize items =>
      String.join (items.map toLatexMath)
    | raw latex _ _ => latex
    | math m => mathToLatexMath m

  /-- Render a math fragment in LaTeX math mode.
      Variables render bare (already italic); doc content
      uses math-aware rendering. -/
  partial def mathToLatexMath : MathDoc → String
    | .var s => escapeLatexMath s
    | .doc d => d.toLatexMath
    | .sym s => s.toLatexMath
    | .seq ds => String.join (ds.map mathToLatexMath)
end

/-- Render a Lean type name to LaTeX math mode. -/
def typeToLatexMath (s : String) : String :=
  let s := s.trimAscii.toString
  match s with
  | "Nat" => "\\mathbb{N}"
  | "String" => "\\text{String}"
  | other =>
    "\\text{" ++ escapeLatexMath other ++ "}"

mutual
  /-- Render a document to Typst. -/
  partial def toTypst : Doc → String
    | plain s => s
    | bold d => s!"*{d.toTypst}*"
    | italic d => s!"_{d.toTypst}_"
    | code s => s
    | seq ds => String.join (ds.map toTypst)
    | line => "\n"
    | itemize items =>
      let body := items.map fun d =>
        s!"- {d.toTypst}"
      String.intercalate "\n" body
    | raw _ typst _ => typst
    | math m => mathToTypst m

  /-- Render a math fragment to Typst. -/
  partial def mathToTypst : MathDoc → String
    | .var s => s
    | .doc d => d.toTypst
    | .sym s => s.toPlainText
    | .seq ds => String.join (ds.map mathToPlainText)
end

mutual
  /-- Render a document to HTML. -/
  partial def toHTML : Doc → String
    | plain s => s
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
    | math m => mathToHTML m

  /-- Render a math fragment to HTML. -/
  partial def mathToHTML : MathDoc → String
    | .var s => s!"<i>{s}</i>"
    | .doc d => d.toHTML
    | .sym .langle => "&langle;"
    | .sym .rangle => "&rangle;"
    | .sym .lbracket => "&lbrack;"
    | .sym .rbracket => "&rbrack;"
    | .sym .lparen => "("
    | .sym .rparen => ")"
    | .seq ds => String.join (ds.map mathToHTML)
end

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
