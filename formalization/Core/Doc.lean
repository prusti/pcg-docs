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
  /-- Equal: `=` (with surrounding spaces). -/
  | eq
  /-- Existential quantifier: `∃` (with trailing space). -/
  | exists_
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
  /-- Set intersection: `∩` (with surrounding spaces). -/
  | cap
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
  /-- Greek lowercase pi: `π`. -/
  | pi
  /-- Greek lowercase mu: `μ`. -/
  | mu
  /-- Greek lowercase alpha: `α`. -/
  | alpha
  /-- Greek lowercase theta: `θ`. -/
  | theta
  /-- Greek lowercase phi (loopy form): `ϕ`. -/
  | phi
  /-- Greek lowercase phi (curly form): `φ`. -/
  | varphi
  /-- Semicolon: `;`. -/
  | semicolon
  /-- Auto-sized left paren: `\left(` in LaTeX. Use when
      the wrapped content contains a multi-line construct
      (e.g. a `match` that produces `\begin{array}` rows)
      so the paren grows to match its height. -/
  | lparenAuto
  /-- Auto-sized right paren: `\right)` in LaTeX. -/
  | rparenAuto
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
    /-- Wide tilde accent: `\widetilde{...}`. -/
    | widetilde (d : MathDoc)
    /-- Hat accent: `\hat{...}`. -/
    | hat (d : MathDoc)
    /-- Subscript: `base_{sub}` (e.g. `t_D`). -/
    | sub (base : MathDoc) (sub : MathDoc)
    /-- Concatenation of mathematical documents. -/
    | seq (ds : List MathDoc)
    | space
    /-- Soft line break (presentation-only). The LaTeX
        backend lifts a `seq` containing breaks into a
        single-column array environment so each break
        renders as an actual line. Plain-text / Typst /
        HTML backends render this as a space. -/
    | break_
    /-- Indent the wrapped content by `n` half-em units.
        LaTeX renders as `\hskip{n*0.5em}`; other backends
        pass `body` through. -/
    | indent (n : Nat) (body : MathDoc)
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

/-- Coercion so that string literals can stand in for `Doc`
    descriptions in DSL constructs (e.g. `defStruct` field
    docs). The string is wrapped as `Doc.plain`. -/
instance : Coe String Doc := ⟨.plain⟩

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
  | .eq => " = "
  | .exists_ => "∃ "
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
  | .cap => " ∩ "
  | .leftarrow => " ← "
  | .assign => " := "
  | .append => " ++ "
  | .pipe => "|"
  | .lambda => "λ "
  | .pi => "π"
  | .mu => "μ"
  | .alpha => "α"
  | .theta => "θ"
  | .phi => "ϕ"
  | .varphi => "φ"
  | .semicolon => ";"
  | .lparenAuto => "("
  | .rparenAuto => ")"

end MathSym

namespace MathDoc

/-- Text in math mode (rendered as `\text{s}` in LaTeX). -/
def text (s : String) : MathDoc := .doc (.plain s)

/-- Whether a math doc contains a multi-line LaTeX construct
    (`\begin{array}` or `\left…`) that forces its surrounding
    delimiters to grow. Used by `paren` to choose between
    fixed-size `(`/`)` and auto-sized `\left(`/`\right)`. -/
partial def containsAutoSize : MathDoc → Bool
  | .raw s =>
    let hasSubstr (needle : String) : Bool :=
      (s.splitOn needle).length > 1
    hasSubstr "\\begin{array}" || hasSubstr "\\left"
  | .space => false
  | .doc d =>
    -- `rawMath s` (used by `match_` etc.) wraps the LaTeX
    -- through `.doc (.raw …)`, so descend into `Doc.raw`
    -- to spot `\begin{array}` and friends.
    let rec docHasAutoSize : Doc → Bool
      | .raw latex _ _ =>
        let hasSubstr (needle : String) : Bool :=
          (latex.splitOn needle).length > 1
        hasSubstr "\\begin{array}" || hasSubstr "\\left"
      | .seq ds => ds.any docHasAutoSize
      | .bold d | .italic d
      | .underline _ d => docHasAutoSize d
      | .link t _ => docHasAutoSize t
      | .itemize ds => ds.any docHasAutoSize
      | .math m => m.containsAutoSize
      | .plain _ | .code _ | .line => false
    docHasAutoSize d
  | .seq ds => ds.any containsAutoSize
  | .bb d | .bold d | .italic d | .cal d
  | .widetilde d | .hat d => d.containsAutoSize
  | .sub b s => b.containsAutoSize || s.containsAutoSize
  | .sym _ => false
  -- A `seq` containing `.break_` lifts to `\begin{array}`,
  -- so its surrounding parens must grow.
  | .break_ => true
  | .indent _ body => body.containsAutoSize

/-- Whether a math doc contains a `Doc.link` anywhere within
    its sub-tree. Used at hyperlink-wrapping sites (e.g. the
    inductive-property `displayed` template in
    `DslExpr.toDoc`) to avoid emitting a `\hyperlink{...}{...}`
    whose body already contains another `\hyperlink` —
    nested PDF link annotations cause readers to honour the
    *outer* annotation, swallowing clicks on the inner one.
    Skipping the outer wrap when an inner link is present
    leaves the more-specific link clickable. -/
partial def containsLink : MathDoc → Bool
  | .doc d =>
    let rec docHasLink : Doc → Bool
      | .link _ _ => true
      | .seq ds => ds.any docHasLink
      | .bold d | .italic d => docHasLink d
      | .underline _ d => docHasLink d
      | .itemize ds => ds.any docHasLink
      | .math m => m.containsLink
      | .plain _ | .code _ | .line | .raw .. => false
    docHasLink d
  | .seq ds => ds.any containsLink
  | .bb d | .bold d | .italic d | .cal d
  | .widetilde d | .hat d => d.containsLink
  | .sub b s => b.containsLink || s.containsLink
  | .indent _ body => body.containsLink
  | .raw _ | .sym _ | .space | .break_ => false

/-- Wrap a math doc in parentheses. Switches to LaTeX
    `\left(`/`\right)` when the content contains a
    multi-line construct so the parens grow to match. -/
def paren (d : MathDoc) : MathDoc :=
  if d.containsAutoSize then
    .seq [.sym .lparenAuto, d, .sym .rparenAuto]
  else
    .seq [.sym .lparen, d, .sym .rparen]

/-- Wrap a math doc in square brackets. -/
def bracket (d : MathDoc) : MathDoc :=
  .seq [.sym .lbracket, d, .sym .rbracket]

/-- Wrap a math doc in curly braces. -/
def brace (d : MathDoc) : MathDoc :=
  .seq [.sym .lbrace, d, .sym .rbrace]

end MathDoc

namespace Doc

/-- Unicode-to-LaTeX replacement pairs. Each pair is
    `(unicode, textMode, mathMode)`. -/
private def latexReplacements :
    List (String × String × String) :=
  [ ("_", "\\_", "\\_")
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
  , ("≠", "$\\neq$", "\\neq")
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
  , ("₁", "$_1$", "_1")
  , ("₂", "$_2$", "_2")
  , ("₃", "$_3$", "_3")
  , ("₄", "$_4$", "_4")
  , ("₅", "$_5$", "_5")
  , ("₆", "$_6$", "_6")
  , ("₇", "$_7$", "_7")
  , ("₈", "$_8$", "_8")
  , ("₉", "$_9$", "_9")
  , ("⟨", "$\\langle$", "\\langle{}")
  , ("⟩", "$\\rangle$", "\\rangle{}")
  , ("Δ", "$\\Delta$", "\\Delta")
  , ("′", "\\ensuremath{'}", "'")
  ]

/-- Translate Unicode symbols to LaTeX commands (text mode). -/
def escapeLatex : String → String :=
  fun s => latexReplacements.foldl
    (fun acc (from_, to, _) => acc.replace from_ to) s

/-- Like `escapeLatex`, but also renders apostrophes as
    upward-tick primes (for code identifiers). Additionally,
    a zero-width `\allowbreak` is inserted after `/` so that
    paths like `\texttt{definitions/places.md}` can be broken
    across lines without producing an overfull `\hbox`. -/
def escapeLatexCode : String → String :=
  fun s => (escapeLatex s).replace "'" "\\ensuremath{'}"
    |>.replace "/" "/\\allowbreak{}"

/-- Transform a function / identifier name so trailing-prime
    apostrophes render as upward-tick primes (e.g. `foo'` →
    `foo′`). The Unicode prime is in turn mapped to
    `\ensuremath{'}` by `escapeLatex`. -/
def fnNameDisplay (s : String) : String :=
  s.replace "'" "′"

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
    | .space => " "
    | .raw s => s
    | .doc d => d.toPlainText
    | .sym s => s.toPlainText
    | .bb d | .bold d | .italic d | .cal d
    | .widetilde d | .hat d =>
      mathToPlainText d
    | .sub base s =>
      s!"{mathToPlainText base}_{mathToPlainText s}"
    | .seq ds => String.join (ds.map mathToPlainText)
    | .break_ => " "
    | .indent _ body => mathToPlainText body
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
    | .space => " "
    | .raw s => s
    | .doc d => d.toTypst
    | .sym s => s.toPlainText
    | .bb d => s!"bb({mathToTypst d})"
    | .bold d => s!"bold({mathToTypst d})"
    | .italic d => s!"italic({mathToTypst d})"
    | .cal d => s!"cal({mathToTypst d})"
    | .widetilde d => s!"tilde({mathToTypst d})"
    | .hat d => s!"hat({mathToTypst d})"
    | .sub base s =>
      s!"{mathToTypst base}_({mathToTypst s})"
    | .seq ds => String.join (ds.map mathToTypst)
    | .break_ => " "
    | .indent _ body => mathToTypst body
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
    | .space => "&nbsp;"
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
    | .sym .eq => " = "
    | .sym .exists_ => "&exist; "
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
    | .sym .cap => " &cap; "
    | .sym .leftarrow => " &larr; "
    | .sym .assign => " := "
    | .sym .append => " ++ "
    | .sym .pipe => "|"
    | .sym .lambda => "&lambda; "
    | .sym .pi => "&pi;"
    | .sym .mu => "&mu;"
    | .sym .alpha => "&alpha;"
    | .sym .theta => "&theta;"
    | .sym .phi => "&phi;"
    | .sym .varphi => "&phi;"
    | .sym .semicolon => ";"
    | .sym .lparenAuto => "("
    | .sym .rparenAuto => ")"
    | .bb d | .bold d => s!"<b>{mathToHTML d}</b>"
    | .italic d => s!"<i>{mathToHTML d}</i>"
    | .cal d => mathToHTML d
    | .widetilde d => s!"<span style=\"text-decoration: overline\
         dashed\">{mathToHTML d}</span>"
    | .hat d => s!"{mathToHTML d}\u0302"
    | .sub base s =>
      s!"{mathToHTML base}<sub>{mathToHTML s}</sub>"
    | .seq ds => String.join (ds.map mathToHTML)
    | .break_ => "<br>\n"
    | .indent _ body => mathToHTML body
end

end Doc
