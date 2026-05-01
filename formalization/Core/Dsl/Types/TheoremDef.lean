import Core.Dsl.Types.DslExpr

/-- A `defTheorem`-registered theorem definition.

    A theorem records the *statement* of a DSL-level proposition
    (typically the application of a `defProperty` to specific
    arguments) together with the name of an existing Lean term
    that proves it. The presentation exporter renders each
    registered theorem in its module's body as a `theorem`
    LaTeX environment containing the displayed statement and
    a `\proof` block reading "proved in `<proofIdent>`". -/
structure TheoremDef where
  /-- The theorem's identifier (used for the `\hypertarget` /
      `\label` anchor and as the displayed name). -/
  name : String
  /-- A short description rendered as prose under the theorem
      header. -/
  doc : Doc
  /-- The DSL-level statement of the theorem. Typically a
      property application like `FramingInvariant ⟨m, pcg⟩` or
      a `∀∀ … . property ⟨…⟩` quantification. -/
  statement : DslExpr
  /-- The Lean identifier of the proof. Rendered in the
      presentation as the target of the `\proof` block — the
      reader is told the theorem is "proved in `<proofIdent>`". -/
  proofIdent : String
  deriving Repr

namespace TheoremDef

/-- Render the theorem as a LaTeX environment: a `theorem`
    block containing the displayed statement, followed by a
    `proof` block that says where the theorem is proved.

    The displayed statement is rendered via `DslExpr.toDoc`
    (with `isProperty := true` so property applications
    surface as their displayed math), then wrapped in a
    `\[...\]` display-math equation. -/
def formalDefLatex (t : TheoremDef) (ctx : RenderCtx) : Latex :=
  let anchor : Latex :=
    .raw s!"\\hypertarget\{theorem:{t.name}}\{}\\label\{theorem:{t.name}}"
  let stmtMath : LatexMath :=
    (t.statement.toDoc t.name ctx (isProperty := true)).toLatexMath
  let theoremBlock : Latex :=
    .envOpts "theorem"
        (.text (Doc.fnNameDisplay t.name)) (.seq [
      anchor, .newline,
      t.doc.toLatex, .newline,
      .displayMath stmtMath
    ])
  let proofBlock : Latex :=
    .env "proof"
      (.seq [.text "Proved in ",
             .texttt (.text t.proofIdent), .text "."])
  .seq [theoremBlock, .newline, proofBlock]

end TheoremDef
