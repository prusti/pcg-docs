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
  deriving DecidableEq, Repr, Hashable

/-! `Std.HashMap.getElem?_eq_some_iff_…` (used to recover
    `(_, ptr) ∈ frame.locals.toList` from
    `mapGet frame.locals l = some ptr` in StackFrame's
    `storageDead`) needs `EquivBEq` and `LawfulHashable` on the
    key. Those follow from `LawfulBEq`, whose derive needs a
    *structural* `BEq` — adding `BEq` to the `defStruct`
    deriving list installs a `DecidableEq`-driven `BEq` whose
    `decide` unfolding defeats the `LawfulBEq` derive. The
    same-shaped block in `MIR/Body.lean` does this for
    `BasicBlockIdx`. -/
defRaw after =>
deriving instance BEq for Local
defRaw after =>
deriving instance ReflBEq for Local
defRaw after =>
deriving instance LawfulBEq for Local

defStruct FieldIdx (.raw "f", .raw "F")
  "Field Indices"
  (.plain "A field index within a struct or tuple.")
  constructor "FieldIdx"
where
  | index "The field index." : Nat

defStruct VariantIdx (.raw "V",
    .text "VariantIdx")
  "Variant Indices"
  (.plain "A variant index within an enum.")
  constructor "VariantIdx"
where
  | index "The variant index." : Nat

-- Same `decide`-vs-structural workaround as `Local`, applied to
-- `FieldIdx` and `VariantIdx`: `LawfulBEq ProjElem` (and hence
-- `LawfulBEq Place`) needs structural `BEq` on every field type.
defRaw after =>
deriving instance BEq for FieldIdx
defRaw after =>
deriving instance ReflBEq for FieldIdx
defRaw after =>
deriving instance LawfulBEq for FieldIdx

defRaw after =>
deriving instance BEq for VariantIdx
defRaw after =>
deriving instance ReflBEq for VariantIdx
defRaw after =>
deriving instance LawfulBEq for VariantIdx

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
  | downcast (variant : VariantIdx)
    "Downcast an enum to a specific variant."
    (mathdoc! "@{variant}")
  deriving Repr, BEq, Hashable

-- `ProjElem` is *not* a nested inductive — it only refers to
-- already-lawful types (`FieldIdx`, `Ty`, `Local`, `VariantIdx`)
-- — so the standard `LawfulBEq` derive succeeds.
deriving instance ReflBEq, LawfulBEq for ProjElem

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
deriving instance ReflBEq, LawfulBEq for Place

defAlias RETURN = Place⟨Local⟨0⟩, []⟩
