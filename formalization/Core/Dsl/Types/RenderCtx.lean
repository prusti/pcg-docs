import Core.Dsl.Types.EnumDef

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
      it is qualified by module (`fn:InitTree.join`). -/
  knownFnAnchors : String → Bool := fun _ => false
  /-- When rendering a function body, the enclosing function's
      module's last segment (e.g. `"InitTree"` when rendering
      `PCG.Owned.InitTree.join`'s body). Used to resolve
      unqualified ambiguous calls to the most likely
      fully-qualified anchor: a bare `join` inside
      `PCG.Owned.InitTree` resolves to `#fn:InitTree.join`. -/
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
