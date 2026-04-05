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
    environment. -/
def formalDefLatex (p : PropertyDef) : String :=
  let lb := "{"
  let rb := "}"
  let title := Doc.escapeLatex p.fnDef.name
  s!"\\begin{lb}definition{rb}[{title}]\n\
     {p.definition.toLaTeX}\n\
     \\end{lb}definition{rb}"

end PropertyDef
