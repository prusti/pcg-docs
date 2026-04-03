import Shared.Doc
import Shared.EnumDef

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
  deriving Repr

namespace OrderDef

/-- Look up the plain-text symbol for a variant name. -/
private def lookupSymbol (e : EnumDef) (name : String)
    : String :=
  match e.variants.find? (·.name == name) with
  | some v => v.symbolDoc.toPlainText
  | none => name

/-- Compute the level (longest path to bottom) of each element. -/
private partial def computeLevels
    (elements : List String) (facts : List OrderFact)
    : List (String × Nat) :=
  let childrenOf (x : String) : List String :=
    facts.filter (·.greater == x) |>.map (·.lesser)
  let rec level (x : String) (visited : List String) : Nat :=
    if visited.contains x then 0
    else
      let children := childrenOf x
      if children.isEmpty then 0
      else 1 + children.foldl
        (fun acc c => max acc (level c (x :: visited))) 0
  elements.map fun e => (e, level e [])

/-- Generate a Hasse diagram as a `Doc`.

    Uses tikz for LaTeX, ASCII art for Typst/HTML. -/
def hasseDiagram (o : OrderDef) (e : EnumDef) : Doc :=
  let levels := computeLevels o.elements o.facts
  let maxLvl := levels.foldl (fun acc (_, l) => max acc l) 0
  let grouped : List (Nat × List String) :=
    (List.range (maxLvl + 1)).map fun l =>
      (l, levels.filter (·.2 == l) |>.map (·.1))
  let lb := "{"
  let rb := "}"
  let tikzNodes := grouped.flatMap fun (lvl, names) =>
    let n := names.length
    (List.range names.length |>.zip names).map fun (i, name) =>
      let sym := lookupSymbol e name
      let x : Int := (2 * i : Int) - (n - 1 : Int)
      s!"  \\node ({name}) at ({x}, {lvl}) {lb}{Doc.escapeLatex sym}{rb};"
  let tikzEdges := o.facts.map fun f =>
    s!"  \\draw ({f.greater}) -- ({f.lesser});"
  let tikzLines := [
    s!"\\begin{lb}tikzpicture{rb}[every node/.style={lb}minimum size=6mm{rb}]",
    String.intercalate "\n" tikzNodes,
    String.intercalate "\n" tikzEdges,
    s!"\\end{lb}tikzpicture{rb}"
  ]
  let tikz := String.intercalate "\n" tikzLines
  let ascii := grouped.reverse.map fun (_, names) =>
    let syms := names.map (lookupSymbol e)
    String.intercalate "   " syms
  let asciiStr := String.intercalate "\n" ascii
  let edges := o.facts.map fun f =>
    s!"{lookupSymbol e f.greater} > {lookupSymbol e f.lesser}"
  let edgesStr := String.intercalate ", " edges
  let typstStr := s!"{asciiStr}\n({edgesStr})"
  .raw tikz typstStr typstStr

end OrderDef
