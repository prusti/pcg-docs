import Core.Dsl.Types.FnDef

/-- An exportable property (predicate) definition.

    Wraps a `FnDef` (for Lean/Rust code generation) with
    a `Doc` body for LaTeX presentation as a textual
    definition. -/
structure PropertyDef where
  /-- The underlying function definition (returns Bool). -/
  fnDef : FnDef
  /-- The textual definition body for LaTeX rendering. -/
  definition : Doc
  deriving Repr

namespace PropertyDef

/-- Render the property as a LaTeX definition
    environment followed by an algorithm block. -/
def formalDefLatex
    (p : PropertyDef)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (variants : List VariantDef := [])
    (knownFns : String → Bool := fun _ => false)
    : Latex :=
  let defBlock : Latex :=
    .envOpts "definition" p.fnDef.name
      (.seq [p.definition.toLatex, .newline])
  let algoBlock := p.fnDef.formalDefLatex
    ctorDisplay variants (isProperty := true)
    (knownFns := knownFns)
  .seq [defBlock, .newline, .newline, algoBlock]

end PropertyDef
