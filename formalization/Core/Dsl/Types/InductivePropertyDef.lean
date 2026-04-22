import Core.Export.Latex
import Core.Dsl.Types.StructDef

/-- A binder appearing in an inductive-property rule, e.g.
    `cap : InitialisationState` inside `{cap : InitialisationState}`.
    The `type` is stored as the printed Lean text so that we can
    splice the binder verbatim back into the generated `inductive`
    declaration without round-tripping through `DSLType`. -/
structure InductiveRuleBinder where
  /-- Bound name. -/
  name : String
  /-- Optional type annotation (raw Lean source). -/
  type : Option String
  deriving Repr

/-- A single inference-rule of an inductive property: a list of
    quantified binders, a list of premises (each a Lean term whose
    source is preserved verbatim), and the rule's conclusion (also
    a Lean term).

    The premises and conclusion are kept as plain strings so the
    DSL can emit a Lean `inductive` constructor that delegates to
    Lean's own elaborator for type-checking, while still rendering
    each rule as an inference rule in LaTeX. -/
structure InductiveRule where
  /-- Constructor name (e.g. `"leaf"`, `"fields"`). -/
  name : String
  /-- Universally-quantified binders (rendered above the line as
      a side-condition like `cap, fs, x`). -/
  binders : List InductiveRuleBinder
  /-- Premises (rendered above the inference line, separated by
      thin spaces). Each is a Lean term whose source is preserved
      verbatim. -/
  premises : List String
  /-- Rule conclusion: the predicate applied to its indices,
      preserved as Lean source. -/
  conclusion : String
  deriving Repr

/-- An exportable inductive-property definition. Produces a Lean
    `inductive Name … : Prop` in both the in-tree and generated
    Lean projects, and a sequence of `\inferrule`-rendered
    inference rules in the LaTeX presentation. The Rust exporter
    skips these (Prop-level, no runtime payload). -/
structure InductivePropertyDef where
  /-- The property name (e.g. `"HasNonDeepLeaf"`). -/
  name : String
  /-- Formatted type symbol for document exports. -/
  symbolDoc : MathDoc
  /-- Symbol for the property as a set/relation. -/
  setDoc : MathDoc
  /-- LaTeX definition title (e.g. `"Has Non-Deep Leaf"`). -/
  docParam : String
  /-- Top-level documentation. -/
  doc : Doc
  /-- Implicit type parameters (rare for a Prop, but supported
      symmetrically with `defStruct` / `defEnum`). -/
  typeParams : List String := []
  /-- The property's indices (each becomes an explicit binder in
      the generated `inductive Name (…) : Prop`). -/
  params : List FieldDef
  /-- The inference rules. -/
  rules : List InductiveRule
  /-- Pre-rendered Lean source for the underlying
      `inductive Name … : Prop where | …` declaration. The
      DSL command precomputes this so the LeanExport pipeline
      need not re-derive Lean type strings (which would
      require importing the Lean exporter and creating a
      circular dependency between `Core/Dsl/Types/` and
      `Core/Export/Lean.lean`). -/
  leanSource : String := ""
  deriving Repr

namespace InductivePropertyDef

/-- Render a Lean-source fragment (premise or conclusion) as
    a `LatexMath.raw` with Unicode-to-LaTeX substitution
    applied. We avoid `LatexMath.escaped`, which would wrap
    multi-character identifiers in `\mathit{}` and obscure the
    structure of the term. -/
private def termLatex (s : String) : LatexMath :=
  .raw (Doc.escapeLatexMath s)

/-- Render a single rule as a `\inferrule`. Premises sit
    above the inference line (separated by `\\\\`),
    conclusion below. -/
private def ruleLatex (r : InductiveRule) : Latex :=
  let premiseLines : List LatexMath :=
    r.premises.map termLatex
  let premises : LatexMath :=
    if r.premises.isEmpty then .raw ""
    else
      LatexMath.intercalate (.raw " \\\\ ") premiseLines
  let conclusion : LatexMath := termLatex r.conclusion
  let bindersComment : LatexMath :=
    if r.binders.isEmpty then .raw ""
    else
      let names := ", ".intercalate
        (r.binders.map (·.name))
      -- Render inside `\text{}`, so the bound-variable list
      -- needs to be a plain-text fragment.
      .seq [.raw "\\quad\\text{(for fresh ",
            .raw (names.replace "_" "\\_"),
            .raw ")}"]
  let inference : LatexMath :=
    -- The `Right=` label of `\inferrule*` is rendered in text
    -- mode, so use a raw plain string for the rule name.
    .seq [
      .raw "\\inferrule*[Right=\\textsc{",
      .raw (r.name.replace "_" "\\_"),
      .raw "}]{",
      premises,
      .raw "}{",
      conclusion,
      .raw "}",
      bindersComment ]
  Latex.displayMath inference

/-- Render the inductive property as a LaTeX `definition`
    environment (prose) followed by one `\inferrule` per rule. -/
def formalDefLatex (p : InductivePropertyDef) : Latex :=
  let typeTarget : Latex :=
    .raw s!"\\hypertarget\{type:{p.name}}\{}"
  let paramSig : LatexMath :=
    LatexMath.intercalate (.raw ", ")
      (p.params.map fun f =>
        .seq [.escaped f.name, .raw " : ",
              f.ty.toLatexMath (fun _ => false)])
  let header : LatexMath :=
    .seq [
      p.symbolDoc.toLatexMath,
      .raw " : ", paramSig, .raw " \\to \\mathbf{Prop}" ]
  let prose : Latex := .seq [p.doc.toLatex, .newline]
  let defBlock : Latex :=
    .envOpts "definition" (.text p.docParam) (.seq [
      typeTarget, .newline,
      .displayMath header, .newline ])
  let rulesBlock : Latex :=
    .seq (p.rules.map ruleLatex |>.intersperse .newline)
  .seq [prose, defBlock, .newline, rulesBlock, .newline]

end InductivePropertyDef
