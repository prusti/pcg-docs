import Core.Export.Latex
import Core.Dsl.DslType
import Core.Dsl.Types.DslExpr

/-- An exportable type-or-value alias definition.

    Represents either a type-alias declaration

    ```
    Name T₁ … Tₙ = Body
    ```

    rendered as `abbrev` in Lean and `pub type` in Rust, or a
    value-alias declaration

    ```
    Name = Value
    ```

    rendered as `def Name : Type := Value` in Lean and `pub const
    NAME: Type = Value;` in Rust. The two cases are distinguished
    by `value`: `none` for type aliases, `some e` for value
    aliases (with `aliased` then carrying the value's type). -/
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
  /-- For type aliases: the type this alias expands to.
      For value aliases: the type of the aliased value. -/
  aliased : DSLType
  /-- `none` for type aliases. `some e` for value aliases,
      where `e` is the aliased expression. -/
  value : Option DslExpr := none
  deriving Repr

namespace AliasDef

/-- Render the alias as a LaTeX `definition` environment
    containing the defining equation

    ```
    Name T₁ … Tₙ = Body        -- type alias
    Name = Value : Type        -- value alias
    ```

    For type aliases the RHS is drawn from the underlying
    `DSLType`. For value aliases the RHS is the rendered DSL
    expression and the type is shown after `:` so the reader
    sees both the value and its type. -/
def formalDefLatex (a : AliasDef)
    (knownTypes : String → Bool := fun _ => false) : Latex :=
  let typeParamsLM : LatexMath :=
    .seq (a.typeParams.flatMap fun p =>
      [.raw "~", .var p])
  -- For type aliases, the LHS reads the type's symbol /
  -- set name from `setDoc`. For value aliases the user
  -- supplies no symbol, so we fall back to the alias name
  -- itself so the equation reads `RETURN = …` instead of
  -- a leading-bare `=`.
  let lhsHead : LatexMath :=
    if a.value.isSome then .escaped a.name
    else a.setDoc.toLatexMath
  let lhs : LatexMath := .seq [lhsHead, typeParamsLM]
  let tyLM : LatexMath := a.aliased.toLatexMath knownTypes
  let eqRhs : LatexMath := match a.value with
    | none => tyLM
    | some e =>
      let valLM : LatexMath :=
        (DslExpr.toDoc "" {} (fun _ => none) false e).toLatexMath
      .seq [valLM, .raw " : ", tyLM]
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
      .displayMath (.seq [lhs, .raw " = ", eqRhs]),
      .newline
    ])
  ]

end AliasDef
