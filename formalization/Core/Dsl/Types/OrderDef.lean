import Core.Dsl.Types.EnumDef

/-- A covering relation in a partial order: `greater > lesser`. -/
structure OrderFact where
  greater : String
  lesser : String
  deriving Repr

/-- Metadata for an ordering on a finite enum, used for
    cross-language export and presentation. -/
structure OrderDef where
  /-- The enum type name. -/
  enumName : String
  /-- Variant names (in declaration order). -/
  elements : List String
  /-- The covering relations (Hasse diagram edges). -/
  facts : List OrderFact
  /-- Full reflexive-transitive closure as `(a, b)` where `a ≤ b`. -/
  closure : List (String × String)
  /-- If the order was declared as an inequality chain
      `a > b > ... > z`, this holds the variant names in
      descending order. Used to render the order as a chain
      rather than a Hasse diagram. -/
  chain : Option (List String) := none
  deriving Repr

-- ══════════════════════════════════════════════
-- Hasse diagram rendering
-- ══════════════════════════════════════════════

namespace OrderDef

/-- Look up the plain-text symbol for a variant name. -/
private def lookupSymbol (e : EnumDef) (name : String)
    : String :=
  match e.variants.find? (·.name.name == name) with
  | some v => v.displayDoc.toPlainText
  | none => name

/-- Look up the LaTeX math-mode symbol for a variant. -/
private def lookupSymbolMath
    (e : EnumDef) (name : String) : LatexMath :=
  match e.variants.find? (·.name.name == name) with
  | some v => v.displayLatexMath
  | none => .escaped name

/-- Look up the `MathDoc` symbol for a variant. -/
private def lookupSymbolMathDoc
    (e : EnumDef) (name : String) : MathDoc :=
  match e.variants.find? (·.name.name == name) with
  | some v => v.displayMathDoc
  | none => .doc (.plain name)

/-- Compute the level (longest path to bottom) of
    each element. -/
private partial def computeLevels
    (elements : List String) (facts : List OrderFact)
    : List (String × Nat) :=
  let childrenOf (x : String) : List String :=
    facts.filter (·.greater == x) |>.map (·.lesser)
  let rec level (x : String)
      (visited : List String) : Nat :=
    if visited.contains x then 0
    else
      let children := childrenOf x
      if children.isEmpty then 0
      else 1 + children.foldl
        (fun acc c =>
          max acc (level c (x :: visited))) 0
  elements.map fun e => (e, level e [])

/-- An inequality chain `a > b > ... > z` as a structured
    `MathDoc`: each variant's display symbol joined by
    greater-than signs. -/
private def chainMathDoc
    (e : EnumDef) (chain : List String) : MathDoc :=
  let parts := chain.map (lookupSymbolMathDoc e)
  .seq (parts.intersperse (.sym .gt))

/-- Render the order as displayed LaTeX math
    `\[ a > b > ... > z \]` using the structured
    `MathDoc` representation. -/
private def chainLatex
    (e : EnumDef) (chain : List String) : Latex :=
  .displayMath (chainMathDoc e chain).toLatexMath

/-- Render the order as a Hasse diagram / inequality chain.

    For chain-declared orders, emits displayed math
    `\[ a > b > ... > z \]`. Otherwise emits a tikz
    picture (wrapped in `Latex.raw` as there is no
    structured representation for tikz). -/
def hasseDiagram (o : OrderDef) (e : EnumDef)
    : Latex :=
  match o.chain with
  | some ch => chainLatex e ch
  | none =>
  let levels := computeLevels o.elements o.facts
  let maxLvl := levels.foldl
    (fun acc (_, l) => max acc l) 0
  let grouped : List (Nat × List String) :=
    (List.range (maxLvl + 1)).map fun l =>
      (l, levels.filter (·.2 == l) |>.map (·.1))
  let lb := "{"
  let rb := "}"
  let tikzNodes := grouped.flatMap
    fun (lvl, names) =>
      let n := names.length
      (List.range names.length |>.zip names).map
        fun (i, name) =>
          let sym := (lookupSymbolMath e name).render
          let x : Int :=
            (2 * i : Int) - (n - 1 : Int)
          s!"  \\node ({name}) at ({x}, {lvl}) \
             {lb}${sym}${rb};"
  let tikzEdges := o.facts.map fun f =>
    s!"  \\draw ({f.greater}) -- ({f.lesser});"
  let tikzLines := [
    s!"\\begin{lb}tikzpicture{rb}\
       [every node/.style=\
       {lb}minimum size=6mm{rb}]",
    String.intercalate "\n" tikzNodes,
    String.intercalate "\n" tikzEdges,
    s!"\\end{lb}tikzpicture{rb}"
  ]
  let tikz := String.intercalate "\n" tikzLines
  .raw tikz

end OrderDef

