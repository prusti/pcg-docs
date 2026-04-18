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
  /-- Left brace: { -/
  | lbrace
  /-- Right brace: } -/
  | rbrace
  /-- Empty set: ∅ -/
  | emptySet
  /-- Set membership: ∈ -/
  | setContains
  /-- Non-breaking space. -/
  | space
  /-- Less-than: `<` (with surrounding spaces). -/
  | lt
  /-- Greater-than: `>` (with surrounding spaces). -/
  | gt
  /-- Less-than-or-equal: `≤` (with surrounding spaces). -/
  | le
  /-- Not-equal: `≠` (with surrounding spaces). -/
  | neq
  /-- Addition: `+` (with surrounding spaces). -/
  | add
  /-- Subtraction: `-` (with surrounding spaces). -/
  | sub
  /-- Multiplication: `*` (with surrounding spaces). -/
  | mul
  /-- Division: `/` (with surrounding spaces). -/
  | div
  /-- Logical AND: `∧` (with surrounding spaces). -/
  | land
  /-- Logical OR: `∨` (with surrounding spaces). -/
  | lor
  /-- Implication: `→` (with surrounding spaces). -/
  | implies
  /-- Universal quantifier: `∀` (with trailing space). -/
  | forall_
  /-- Top: `⊤`. -/
  | top
  /-- Bottom: `⊥`. -/
  | bot
  /-- Comma separator: `, `. -/
  | comma
  /-- Dot: `.`. -/
  | dot
  /-- List cons: ` :: `. -/
  | cons
  /-- Underscore wildcard: `_`. -/
  | underscore
  /-- Map-to: `↦` (with surrounding spaces). -/
  | mapsto
  /-- Fat arrow: `⇒` (with surrounding spaces). Used as the
      match-arm separator between pattern and body. -/
  | fatArrow
  /-- Set union: `∪` (with surrounding spaces). -/
  | cup
  /-- Left arrow (monadic bind): `←` (with surrounding spaces). -/
  | leftarrow
  /-- Definition / assignment: ` := `. -/
  | assign
  /-- List append: ` ++ ` (typeset in typewriter). -/
  | append
  /-- Vertical bar: `|` (used for absolute value / length). -/
  | pipe
  /-- Lambda: `λ` (with trailing space). -/
  | lambda
  /-- Semicolon: `;`. -/
  | semicolon
  deriving Repr

/-- Style of an underline: solid or dashed. -/
inductive UnderlineStyle where
  /-- A solid underline. -/
  | solid
  /-- A dashed underline. -/
  | dashed
  deriving Repr, Inhabited

mutual
  /-- A mathematical document fragment, for content that
      appears in math mode (e.g. inside `\[ ... \]`). -/
  inductive MathDoc where
    /-- Raw math content, verbatim. Prefer structured
        constructors (`.sym`, `.seq`, `.bb`, ...) wherever
        possible; only use `.raw` in exceptional cases where
        no structured representation exists. -/
    | raw (s : String)
    /-- A `Doc` rendered in math context (`.plain` becomes
        `\text{}`, `.code` becomes `\mathtt{}`, etc). -/
    | doc (d : Doc)
    /-- A math symbol. -/
    | sym (s : MathSym)
    /-- Blackboard bold: `\mathbb{...}`. -/
    | bb (d : MathDoc)
    /-- Bold: `\mathbb{...}`. -/
    | bold (d : MathDoc)
    /-- Italic: `\mathit{...}`. -/
    | italic (d : MathDoc)
    /-- Calligraphic: `\mathcal{...}`. -/
    | cal (d : MathDoc)
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
        string; backends without a match render the fallback.
        Prefer structured constructors wherever possible; only
        use `.raw` in exceptional cases (e.g. embedding tikz
        pictures) where no structured representation exists. -/
    | raw (latex : String) (typst : String) (html : String)
    /-- Hyperlink: `text` is the visible content, `url` is the
        destination. Rendered backend-appropriately (e.g.
        `\href{url}{text}` in LaTeX, `<a href="url">text</a>`
        in HTML). -/
    | link (text : Doc) (url : String)
    /-- Underlined content. The `style` selects solid
        (`\uline` / `<u>`) vs dashed (`\dashuline` /
        `text-decoration-style: dashed`). -/
    | underline (style : UnderlineStyle) (body : Doc)
    /-- Mathematical content. -/
    | math (m : MathDoc)
    deriving Repr
end

instance : Inhabited Doc := ⟨.plain ""⟩
instance : Inhabited MathDoc := ⟨.raw ""⟩

namespace MathSym

/-- Render to plain text. -/
def toPlainText : MathSym → String
  | .langle => "⟨"
  | .rangle => "⟩"
  | .lbracket => "["
  | .rbracket => "]"
  | .lparen => "("
  | .rparen => ")"
  | .lbrace => "{"
  | .rbrace => "}"
  | .emptySet => "∅"
  | .setContains => "∈"
  | .space => " "
  | .lt => " < "
  | .gt => " > "
  | .le => " ≤ "
  | .neq => " ≠ "
  | .add => " + "
  | .sub => " - "
  | .mul => " * "
  | .div => " / "
  | .land => " ∧ "
  | .lor => " ∨ "
  | .implies => " → "
  | .forall_ => "∀ "
  | .top => "⊤"
  | .bot => "⊥"
  | .comma => ", "
  | .dot => "."
  | .cons => " :: "
  | .underscore => "_"
  | .mapsto => " ↦ "
  | .fatArrow => " ⇒ "
  | .cup => " ∪ "
  | .leftarrow => " ← "
  | .assign => " := "
  | .append => " ++ "
  | .pipe => "|"
  | .lambda => "λ "
  | .semicolon => ";"

end MathSym

namespace MathDoc

/-- Text in math mode (rendered as `\text{s}` in LaTeX). -/
def text (s : String) : MathDoc := .doc (.plain s)

/-- Wrap a math doc in parentheses. -/
def paren (d : MathDoc) : MathDoc :=
  .seq [.sym .lparen, d, .sym .rparen]

/-- Wrap a math doc in square brackets. -/
def bracket (d : MathDoc) : MathDoc :=
  .seq [.sym .lbracket, d, .sym .rbracket]

/-- Wrap a math doc in curly braces. -/
def brace (d : MathDoc) : MathDoc :=
  .seq [.sym .lbrace, d, .sym .rbrace]

end MathDoc

namespace Doc

def brackets (d: MathDoc) : MathDoc :=
  .seq [.sym .lbracket, d, .sym .rbracket]

/-- Interpolate `{def}` in a documentation string, replacing
    each occurrence with inline math `sym ∈ set`. -/
def interpolateDef
    (s : String) (sym set : MathDoc) : Doc :=
  let defDoc : Doc :=
    .math (.seq [sym, .sym .setContains, set])
  let parts := s.splitOn "{def}"
  match parts with
  | [] => .plain ""
  | [single] => .plain single
  | first :: rest =>
    .seq ((.plain first) :: rest.flatMap fun part =>
      [defDoc, .plain part])



/-- Unicode-to-LaTeX replacement pairs. Each pair is
    `(unicode, textMode, mathMode)`. -/
private def latexReplacements :
    List (String × String × String) :=
  [ ("_", "\\_", "_")
  , ("#", "\\#", "\\#")
  , ("%", "\\%", "\\%")
  , ("`", "'", "'")
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
  , ("Π", "$\\Pi$", "\\Pi")
  , ("π", "$\\pi$", "\\pi")
  , ("₀", "$_0$", "_0")
  , ("⟨", "$\\langle$", "\\langle")
  , ("⟩", "$\\rangle$", "\\rangle")
  , ("Δ", "$\\Delta$", "\\Delta")
  ]

/-- Translate Unicode symbols to LaTeX commands (text mode). -/
def escapeLatex : String → String :=
  fun s => latexReplacements.foldl
    (fun acc (from_, to, _) => acc.replace from_ to) s

/-- Like `escapeLatex`, but also renders apostrophes as
    upward-tick primes (for code identifiers). -/
def escapeLatexCode : String → String :=
  fun s => (escapeLatex s).replace "'" "\\ensuremath{'}"

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
    | link text url =>
      s!"{text.toPlainText} ({url})"
    | underline _ body => body.toPlainText
    | math m => mathToPlainText m

  /-- Extract plain text from a math fragment. -/
  partial def mathToPlainText : MathDoc → String
    | .raw s => s
    | .doc d => d.toPlainText
    | .sym s => s.toPlainText
    | .bb d | .bold d | .italic d | .cal d =>
      mathToPlainText d
    | .seq ds => String.join (ds.map mathToPlainText)
end

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
    | link text url =>
      s!"#link(\"{url}\")[{text.toTypst}]"
    | underline .solid body =>
      s!"#underline[{body.toTypst}]"
    | underline .dashed body =>
      s!"#underline(stroke: (dash: \"dashed\"))[{body.toTypst}]"
    | math m => mathToTypst m

  /-- Render a math fragment to Typst. -/
  partial def mathToTypst : MathDoc → String
    | .raw s => s
    | .doc d => d.toTypst
    | .sym s => s.toPlainText
    | .bb d => s!"bb({mathToTypst d})"
    | .bold d => s!"bold({mathToTypst d})"
    | .italic d => s!"italic({mathToTypst d})"
    | .cal d => s!"cal({mathToTypst d})"
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
    | link text url =>
      s!"<a href=\"{url}\">{text.toHTML}</a>"
    | underline .solid body => s!"<u>{body.toHTML}</u>"
    | underline .dashed body =>
      s!"<u style=\"text-decoration-style: dashed\">\
         {body.toHTML}</u>"
    | math m => mathToHTML m

  /-- Render a math fragment to HTML. -/
  partial def mathToHTML : MathDoc → String
    | .raw s => s!"<i>{s}</i>"
    | .doc d => d.toHTML
    | .sym .langle => "&langle;"
    | .sym .rangle => "&rangle;"
    | .sym .lbracket => "&lbrack;"
    | .sym .rbracket => "&rbrack;"
    | .sym .lparen => "("
    | .sym .rparen => ")"
    | .sym .lbrace => "{"
    | .sym .rbrace => "}"
    | .sym .emptySet => "&empty;"
    | .sym .setContains => "&isin;"
    | .sym .space => "&nbsp;"
    | .sym .lt => " &lt; "
    | .sym .gt => " &gt; "
    | .sym .le => " &le; "
    | .sym .neq => " &ne; "
    | .sym .add => " + "
    | .sym .sub => " - "
    | .sym .mul => " * "
    | .sym .div => " / "
    | .sym .land => " &and; "
    | .sym .lor => " &or; "
    | .sym .implies => " &rarr; "
    | .sym .forall_ => "&forall; "
    | .sym .top => "&top;"
    | .sym .bot => "&perp;"
    | .sym .comma => ", "
    | .sym .dot => "."
    | .sym .cons => " :: "
    | .sym .underscore => "_"
    | .sym .mapsto => " &mapsto; "
    | .sym .fatArrow => " &rArr; "
    | .sym .cup => " &cup; "
    | .sym .leftarrow => " &larr; "
    | .sym .assign => " := "
    | .sym .append => " ++ "
    | .sym .pipe => "|"
    | .sym .lambda => "&lambda; "
    | .sym .semicolon => ";"
    | .bb d | .bold d => s!"<b>{mathToHTML d}</b>"
    | .italic d => s!"<i>{mathToHTML d}</i>"
    | .cal d => mathToHTML d
    | .seq ds => String.join (ds.map mathToHTML)
end

end Doc
