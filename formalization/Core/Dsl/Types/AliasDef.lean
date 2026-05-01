import Core.Export.Latex
import Core.Dsl.DslType

/-- An exportable type-alias definition.

    Represents a declaration of the form

    ```
    Name T₁ … Tₙ = Body
    ```

    that is rendered as a `abbrev` in Lean, a `pub type` in Rust,
    and as a `definition` block in the LaTeX presentation. -/
structure AliasDef where
  /-- The alias name (e.g. `"LocalLifetimeProjection"`). -/
  name : String
  /-- Formatted type symbol for document exports. -/
  symbolDoc : MathDoc
  /-- Symbol for the set of all values of this type. -/
  setDoc : MathDoc
  /-- LaTeX definition title (e.g. `"Local Lifetime Projections"`). -/
  docParam : String
  /-- Top-level documentation. -/
  doc : Doc
  /-- Type parameters (e.g. `["P"]` for
      `LocalLifetimeProjection {P}`). -/
  typeParams : List String := []
  /-- The type this alias expands to. -/
  aliased : DSLType
  deriving Repr

namespace AliasDef

/-- Render the alias as a LaTeX `definition` environment
    containing the defining equation

    ```
    Name T₁ … Tₙ = Body
    ```

    with the LHS set-name followed by the type parameters and
    the RHS drawn from the underlying `DSLType`. -/
def formalDefLatex (a : AliasDef)
    (knownTypes : String → Bool := fun _ => false) : Latex :=
  let typeParamsLM : LatexMath :=
    .seq (a.typeParams.flatMap fun p =>
      [.raw "~", .var p])
  let lhs : LatexMath :=
    .seq [a.setDoc.toLatexMath, typeParamsLM]
  let rhs : LatexMath := a.aliased.toLatexMath knownTypes
  -- Both anchors so cross-references via either `#X` (which the
  -- `doc!` macro resolves to `fn:X`) or an explicit `type:X`
  -- target reach the same definition.
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{a.name}}\{}\\hypertarget\{fn:{a.name}}\{}"
  .seq [
    a.doc.toLatex, .newline,
    .envOpts "definition" (.text a.docParam) (.seq [
      typeTarget,
      .newline,
      .displayMath (.seq [lhs, .raw " = ", rhs]),
      .newline
    ])
  ]

end AliasDef
