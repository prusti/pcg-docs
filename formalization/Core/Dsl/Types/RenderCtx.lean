import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.Feature

/-- Lookup/resolver context threaded through LaTeX rendering
    of DSL definitions. -/
structure RenderCtx where
  /-- Map a constructor short name to its display `MathDoc`. -/
  ctorDisplay : String → Option MathDoc := fun _ => none
  /-- All registered enum variants, for argument-symbol
      lookups inside match arms. -/
  variants : List VariantDef := []
  /-- Whether a name refers to a known function (used when
      deciding whether to hyperlink the name). -/
  knownFns : String → Bool := fun _ => false
  /-- Whether a short function name is ambiguous — i.e. more
      than one registered function shares this short name.
      Ambiguous references resolve through
      `resolveFnAnchor` rather than falling back to
      `#fn:{shortName}`. -/
  ambiguousFns : String → Bool := fun _ => false
  /-- Whether a string names an existing `fn:` anchor in the
      LaTeX output. For non-ambiguous functions the anchor is
      the short name (`fn:itPlaces`); for ambiguous functions
      it is qualified by module (`fn:InitTree.meet`). -/
  knownFnAnchors : String → Bool := fun _ => false
  /-- When rendering a function body, the enclosing function's
      module's last segment (e.g. `"InitTree"` when rendering
      `PCG.Owned.InitTree.meet`'s body). Used to resolve
      unqualified ambiguous calls to the most likely
      fully-qualified anchor: a bare `meet` inside
      `PCG.Owned.InitTree` resolves to `#fn:InitTree.meet`. -/
  currentFnModule : Option String := none
  /-- Resolve a short or qualified constructor name to its
      fully-qualified `EnumName.variantName` form. -/
  resolveCtor : String → Option String := fun _ => none
  /-- Resolve a short or qualified constructor name to its
      `VariantDef`. Used to render pattern-matching cases with
      the same display template as the enum definition. -/
  resolveVariant : String → Option VariantDef := fun _ => none
  /-- Whether a name refers to a known struct/enum type. -/
  knownTypes : String → Bool := fun _ => false
  /-- Short-form usage for a property reference
      (rendered inside `\Require` blocks). -/
  precondShortUsage : String → List Doc → Option Doc :=
    fun _ _ => none
  /-- Look up a function's display template and parameter
      names by short name. Used to render call sites with the
      callee's pretty form: each `#param` reference in the
      template is replaced by the rendered argument expression
      at the matching positional slot. Returns `none` for
      functions without a custom display. -/
  resolveFnDisplay : String → Option (List DisplayPart × List String) :=
    fun _ => none
  /-- For a `defInductiveProperty` name, return its `\hypertarget`
      anchor target (e.g. `"fn:Reachable"`) so call sites that
      render via the inductive property's `displayed` template
      can wrap the result in a hyperlink. Returns `none` for
      names that don't refer to a registered inductive property. -/
  inductivePropertyAnchor : String → Option String :=
    fun _ => none
  /-- Look up a struct's display template and field names by
      struct name. Used to render constructor expressions with
      the struct's pretty form: each `#field` reference in the
      template is replaced by the rendered argument at the
      matching positional slot (matched against the struct's
      field declaration order). Returns `none` for structs
      without a custom display template. -/
  resolveStructDisplay : String → Option (List DisplayPart × List String) :=
    fun _ => none
  /-- The number of precondition-proof arguments a registered
      function or property accepts at the end of its argument
      list. Used by the call-site renderer to drop trailing
      precondition proofs when rendering, since they carry no
      information for the reader (the proofs are only needed
      to make the in-process Lean call type-check). Defaults
      to `0` for unknown names. -/
  fnPrecondCount : String → Nat := fun _ => 0
  /-- Whether the current rendering context permits soft line
      breaks emitted via `‹break›` formatting hints. False
      inside `\inferrule*` conclusions and other constructs
      that can't span multiple lines; the `formatHint`
      renderer falls back to rendering the wrapped body
      without the surrounding break. -/
  allowBreak : Bool := true
  /-- Whether a short function name refers to a `defFn`
      marked `implicit`. Such calls render as their lone
      argument alone — the function head is dropped from the
      LaTeX presentation. (The Lean and Rust outputs are
      unaffected; this flag only controls LaTeX rendering.) -/
  implicitFns : String → Bool := fun _ => false
  /-- Whether the given feature is disabled in the current
      presentation. Variants tagged with a disabled feature
      are filtered out by `EnumDef.formalDefLatex`; match
      arms tagged with a disabled feature are filtered out
      by `FnDef.formalDefLatex`, `FnDef.exprLines`, and
      `DslExpr.toDoc`'s `.match_` case. Defaults to
      "everything enabled". -/
  isFeatureDisabled : Feature → Bool := fun _ => false
