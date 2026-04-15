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
  /-- Human-readable `Doc` rendering, parameterised by one
      `Doc` per input parameter. -/
  doc : List Doc → Doc

namespace PropertyDef

/-- Resolve the `doc` by applying the parameter names
    (as plain `Doc`s) in declaration order. Used for the
    LaTeX definition environment. -/
def defaultDoc (p : PropertyDef) : Doc :=
  p.doc (p.fnDef.params.map fun f => .plain f.name)

/-- Render the property as a LaTeX definition
    environment followed by an algorithm block. -/
def formalDefLatex
    (p : PropertyDef)
    (ctorDisplay : String → Option MathDoc :=
      fun _ => none)
    (variants : List VariantDef := [])
    (knownFns : String → Bool := fun _ => false)
    (resolveCtor : String → Option String := fun _ => none)
    (knownTypes : String → Bool := fun _ => false)
    (precondShortUsage :
        String → List Doc → Option Doc :=
      fun _ _ => none)
    : Latex :=
  let defBlock : Latex :=
    .envOpts "definition" p.fnDef.name
      (.seq [p.defaultDoc.toLatex, .newline])
  let algoBlock := p.fnDef.formalDefLatex
    ctorDisplay variants (isProperty := true)
    (knownFns := knownFns) (resolveCtor := resolveCtor)
    (knownTypes := knownTypes)
    (precondShortUsage := precondShortUsage)
  .seq [defBlock, .newline, .newline, algoBlock]

end PropertyDef
