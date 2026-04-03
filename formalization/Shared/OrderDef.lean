import Shared.Doc
import Shared.Rust

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

/-- The `std::cmp::Ordering` path. -/
private def ordPath (variant : String) : RustPath :=
  ⟨["std", "cmp", "Ordering", variant]⟩

/-- Build a `Some(std::cmp::Ordering::X)` expression. -/
private def ordExpr (variant : String) : RustExpr :=
  .call (.path (ordPath variant)) []

/-- Build a match arm comparing two enum variants. -/
private def cmpArm
    (a b : String) (result : RustExpr) : RustMatchArm :=
  .mk (.tuple [.selfVariant a, .selfVariant b]) result

/-- Generate a `PartialOrd` impl from this order. -/
def toRustPartialOrd (o : OrderDef) : RustItem :=
  let selfTy := RustTy.self_
  let selfRef := RustTy.refTo selfTy
  let retTy := RustTy.generic ⟨["Option"]⟩
    [.path (⟨["std", "cmp", "Ordering"]⟩)]
  let equalExpr := RustExpr.some_ (.path (ordPath "Equal"))
  let eqCheck : RustExpr :=
    .«if»
      (.binOp .eq (.path (RustPath.simple "self"))
        (.path (RustPath.simple "other")))
      (.block [.expr (.«return» (some equalExpr))] none)
      none
  let arms := o.elements.flatMap fun a =>
    o.elements.filterMap fun b =>
      if a == b then Option.none
      else
        let ca := capitalise a
        let cb := capitalise b
        let aLeB := o.closure.any fun (x, y) => x == a && y == b
        let bLeA := o.closure.any fun (x, y) => x == b && y == a
        if aLeB then
          some (cmpArm ca cb (RustExpr.some_ (.path (ordPath "Less"))))
        else if bLeA then
          some (cmpArm ca cb (RustExpr.some_ (.path (ordPath "Greater"))))
        else
          some (cmpArm ca cb RustExpr.none_)
  let wildArm : RustMatchArm :=
    .mk (.tuple [.wild, .wild]) RustExpr.none_
  let matchExpr : RustExpr :=
    .«match»
      (.tuple [.path (RustPath.simple "self"), .path (RustPath.simple "other")])
      (arms ++ [wildArm])
  let body : RustExpr :=
    .block [.expr eqCheck] (some matchExpr)
  let partialCmpFn : RustFn :=
    { vis := .priv
      name := "partial_cmp"
      params :=
        [ .selfRef
        , .named (.ident "other") selfRef ]
      retTy := some retTy
      body := body }
  .impl_
    (some ⟨["PartialOrd"]⟩) ⟨[o.enumName]⟩ [partialCmpFn]

end OrderDef
