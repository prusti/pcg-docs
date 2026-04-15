import Core.Dsl.Types.FnDef

/-- An exportable property (predicate) definition.

    Wraps a `FnDef` (for Lean/Rust code generation) with
    a textual definition body for LaTeX presentation.
    The definition is a function of the parameter docs
    (one `Doc` per input), so each usage can weave the
    parameter documentation into the prose. -/
structure PropertyDef where
  /-- The underlying function definition (returns Bool). -/
  fnDef : FnDef
  /-- The textual definition body for LaTeX rendering,
      parameterised by one `Doc` per input parameter. -/
  definition : List Doc → Doc

namespace PropertyDef

/-- Resolve the definition `Doc` by applying the parameter
    docs in declaration order. -/
def definitionDoc (p : PropertyDef) : Doc :=
  p.definition (p.fnDef.params.map fun f => .plain f.doc)

/-- Render the property as a LaTeX definition
    environment followed by an algorithm block. -/
def formalDefLatex
    (p : PropertyDef)
    (ctorDisplay : String → Option LatexMath :=
      fun _ => none)
    (variants : List VariantDef := [])
    (knownFns : String → Bool := fun _ => false)
    (knownCtors : String → Bool := fun _ => false)
    (knownTypes : String → Bool := fun _ => false)
    : Latex :=
  let defBlock : Latex :=
    .envOpts "definition" p.fnDef.name
      (.seq [p.definitionDoc.toLatex, .newline])
  let algoBlock := p.fnDef.formalDefLatex
    ctorDisplay variants (isProperty := true)
    (knownFns := knownFns) (knownCtors := knownCtors)
    (knownTypes := knownTypes)
  .seq [defBlock, .newline, .newline, algoBlock]

end PropertyDef
