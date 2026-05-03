import MIR.Ty
import Core.Dsl.DefAlias
import Core.Dsl.DefRaw

defStruct Local (.raw "l", .raw "L")
  "Locals"
  (doc! "A local $_l_ ∈ _L_$ is a \
    variable in the MIR, identified by index.")
  constructor "LocalIdx"
where
  | index "The local variable index." : Nat
  deriving DecidableEq, Repr, BEq, Hashable

/-! `Std.HashMap.getElem?_eq_some_iff_…` (used to recover
    `(_, ptr) ∈ frame.locals.toList` from
    `mapGet frame.locals l = some ptr` in StackFrame's
    `storageDead`) needs `EquivBEq` and `LawfulHashable` on the
    key, both of which follow from `LawfulBEq`. The defStruct's
    `BEq` derive (above) installs a structural `BEq` directly —
    matching the `BEq` the export auto-adds to the generated
    module — so the lawful derive below picks the same instance
    in both builds. -/
defRaw after => {
deriving instance ReflBEq for Local
deriving instance LawfulBEq for Local
}

defStruct FieldIdx (.raw "f", .raw "F")
  "Field Indices"
  (.plain "A field index within a struct or tuple.")
  constructor "FieldIdx"
where
  | index "The field index." : Nat
  deriving DecidableEq, Repr, BEq, Hashable

defStruct VariantIdx (.raw "V",
    .text "VariantIdx")
  "Variant Indices"
  (.plain "A variant index within an enum.")
  constructor "VariantIdx"
where
  | index "The variant index." : Nat
  deriving DecidableEq, Repr, BEq, Hashable

-- `LawfulBEq ProjElem` (and hence `LawfulBEq Place`) needs
-- structural `BEq` and lawful equality on every field type, so
-- propagate `ReflBEq` / `LawfulBEq` through `FieldIdx` and
-- `VariantIdx` here.
defRaw after => {
deriving instance ReflBEq for FieldIdx
deriving instance LawfulBEq for FieldIdx
}

defRaw after => {
deriving instance ReflBEq for VariantIdx
deriving instance LawfulBEq for VariantIdx
}

defEnum ProjElem (.raw "π", .raw "Π")
  "Projection Elements"
  (doc! "A projection element applied to a place. See `definitions/places.md`.")
where
  | deref
    "Dereference a pointer or reference."
    (MathDoc.doc (.code "*"))
  | field (idx : FieldIdx) (ty : Ty)
    "Access a field by index."
    (mathdoc! ".{idx} : {ty}")
  | index (idx : Local)
    "Index into an array or slice."
    (mathdoc! "[{idx}]")
  | [feature ENUM_TYPES] downcast (variant : VariantIdx)
    "Downcast an enum to a specific variant."
    (mathdoc! "@{variant}")
  deriving Repr, BEq, Hashable

-- `ProjElem` is *not* a nested inductive — it only refers to
-- already-lawful types (`FieldIdx`, `Ty`, `Local`, `VariantIdx`)
-- — so the standard `LawfulBEq` derive succeeds.
defRaw after => {
deriving instance ReflBEq for ProjElem
deriving instance LawfulBEq for ProjElem
}

defStruct Place (.raw "p", .raw "P")
  "Places"
  (doc! "A place in the MIR: a local with a projection. See `definitions/places.md`.")
where
  | «local» "The local variable." : Local
  | projection "The list of projection elements."
      : List ProjElem
  deriving Repr, BEq, Hashable

-- `LawfulBEq (List ProjElem)` is provided by stdlib whenever
-- `LawfulBEq ProjElem` is in scope; combined with `LawfulBEq
-- Local`, that gives `LawfulBEq Place`.
defRaw after => {
deriving instance ReflBEq for Place
deriving instance LawfulBEq for Place
}

-- `LawfulHashable Place` lets `Std.HashSet`/`Std.HashMap` lemmas
-- (`mem_insert`, `mem_union_iff`, `mem_toList`, …) discharge
-- against a `Set Place` or `Map _ Place`. The standard "two
-- equal-by-`BEq` values hash the same" proof goes via
-- `LawfulBEq.eq_of_beq` followed by `rfl` on the now-equal
-- inputs.
defRaw after =>
instance : LawfulHashable Place where
  hash_eq {a b} h := by
    have heq : a = b := LawfulBEq.eq_of_beq h
    subst heq; rfl

defAlias RETURN = Place⟨Local⟨0⟩, []⟩
