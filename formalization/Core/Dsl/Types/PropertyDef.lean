import Core.Dsl.Types.FnDef

/-- An exportable property (predicate) definition.

    Wraps a `FnDef` (for Lean/Rust code generation) with a
    parameterised human-readable `Doc`. The `doc` is a
    function of the parameter docs (one `Doc` per input)
    so each call site can weave its own argument names into
    the rendering — used both for the LaTeX definition
    environment and for `Require` preconditions. -/
structure PropertyDef where
  /-- The underlying function definition (returns Bool). -/
  fnDef : FnDef
  /-- Long-form human-readable `Doc` rendering for the
      property's definition box, parameterised by one `Doc`
      per input parameter. -/
  doc : List Doc → Doc
  /-- Short-form `Doc` rendering for `Require` preconditions,
      also parameterised by one `Doc` per input parameter.
      Rendered as a hyperlink to this property's definition
      so a reader can jump from the precondition to the long
      description. -/
  shortDoc : List Doc → Doc

namespace PropertyDef

/-- Resolve the `doc` by applying the parameter names
    (as plain `Doc`s) in declaration order. Used for the
    LaTeX definition environment. -/
def defaultDoc (p : PropertyDef) : Doc :=
  p.doc (p.fnDef.params.map fun f => .plain f.name)

/-- Render the property as a LaTeX definition
    environment followed by an algorithm block.

    `labelKey` overrides the `\hypertarget` / `\label` key
    used for the underlying function's anchor (see
    `FnDef.formalDefLatex`). -/
def formalDefLatex
    (p : PropertyDef)
    (ctx : RenderCtx := {})
    (labelKey : Option String := none)
    : Latex :=
  let anchor : Latex :=
    .raw s!"\\hypertarget\{property:{p.fnDef.name}}\{}"
  let defBlock : Latex :=
    .envOpts "definition" (.text p.fnDef.name)
      (.seq [anchor, p.defaultDoc.toLatex, .newline])
  let algoBlock := p.fnDef.formalDefLatex ctx
    (isProperty := true) (labelKey := labelKey)
  .seq [defBlock, .newline, .newline, algoBlock]

end PropertyDef
