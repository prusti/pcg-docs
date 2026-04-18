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
  /-- Resolve a short or qualified constructor name to its
      fully-qualified `EnumName.variantName` form. -/
  resolveCtor : String → Option String := fun _ => none
  /-- Whether a name refers to a known struct/enum type. -/
  knownTypes : String → Bool := fun _ => false
  /-- Short-form usage for a property reference
      (rendered inside `\Require` blocks). -/
  precondShortUsage : String → List Doc → Option Doc :=
    fun _ _ => none
