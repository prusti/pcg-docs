import MIR.Region
import Core.Dsl.DefFn
import Core.Dsl.DefRaw

defStruct TyCtorName (.raw "T",
    .text "TyCtorName")
  "Type Constructor Names"
  (.plain "A type constructor name, representing an ADT or \
   primitive type.")
where
  | name "The constructor name." : String
  deriving DecidableEq, Repr, BEq, Hashable

defStruct AliasTyName (.raw "A",
    .text "AliasTyName")
  "Alias Type Names"
  (.plain "An associated type name.")
where
  | name "The associated type name." : String
  deriving DecidableEq, Repr, BEq, Hashable

defEnum Size (.raw "sz", .raw "Size")
  "Integer Sizes"
  (.plain "The size of an integer type.")
where
  | bits (n : Nat)
    "A fixed bit width."
    (mathdoc! "#bits n")
  | ptrSize
    "Pointer-sized."
  deriving DecidableEq, Repr, BEq, Hashable

defFn sizeBytes (.plain "size_bytes")
  (doc! "Number of bytes occupied by an integer of \
    this size. `ptrSize` is hardcoded to 8 bytes \
    (64-bit target).")
  (sz "The integer size." : Size)
  : Nat where
  | .bits n => (n + 7) / 8
  | .ptrSize => 8

defStruct IntType (.raw "it", .raw "IntType")
  "Integer Types"
  (.plain "An integer type, parameterised by signedness and size.")
where
  | signed "Whether the integer is signed." : Bool
  | size "The size of the integer." : Size
  deriving DecidableEq, Repr, BEq, Hashable

defEnum Mutability (.raw "m", .raw "M")
  "Mutabilities"
  (.plain "Mutability of a reference.")
where
  | shared
    "Shared"
  | mutable
    "Mutable"
    (MathDoc.text "mut")
  deriving DecidableEq, Repr, BEq, Hashable

defEnum Ty (.raw "τ", .raw "Ty")
  "Types"
  (doc! "A type in the MIR. See `definitions/types.md`.")
where
  | bool
    "The boolean type."
  | int (it : IntType)
    "An integer type."
    (mathdoc! "#intTy it")
  | param (index : Nat)
    "A type parameter."
    (mathdoc! "#param i")
  | alias (base : Ty) (name : AliasTyName)
      (args : List Ty)
    "An alias type."
    (mathdoc! "{base}::{name}⟨τ̄⟩")
  | ctor (name : TyCtorName) (args : List Ty)
    "A type constructor application."
    (mathdoc! "{name}⟨τ̄⟩")
  | ref (region : Region) (mutability : Mutability)
      (pointee : Ty)
    "A reference type."
    (mathdoc! "&{region} {mutability} {pointee}")
  | box (inner : Ty)
    "A box type."
  | array (elem : Ty) (len : Nat)
    "A fixed-size array type."
    (mathdoc! "[{elem}; n]")
  deriving Repr, Hashable

-- `bool` rather than `.param 0` because the operational
-- semantics' size lookup (`Ty.sizeOf`) requires `IsSized`,
-- and `bool` is sized while `param` is not. Using a sized
-- default lets out-of-bounds `decls[i]!` accesses (the
-- pessimistic fallback) discharge the `IsSized` precondition
-- trivially in proofs that come from `validBody`.
instance : Inhabited Ty where
  default := .bool

-- `Std.HashMap` / `Std.HashSet` membership simp lemmas need
-- `EquivBEq` and `LawfulHashable` on the key type, which both
-- follow from `LawfulBEq`. The structural `BEq` derives in each
-- defStruct/defEnum's `deriving` clause (above) install the
-- structural `BEq` directly — matching what the export auto-adds
-- — so the lawful derives below pick the same instance in both
-- builds.
defRaw after => {
deriving instance ReflBEq, LawfulBEq for RegionVid
deriving instance ReflBEq, LawfulBEq for EarlyBoundRegion
deriving instance ReflBEq, LawfulBEq for Region
deriving instance ReflBEq, LawfulBEq for TyCtorName
deriving instance ReflBEq, LawfulBEq for AliasTyName
deriving instance ReflBEq, LawfulBEq for Size
deriving instance ReflBEq, LawfulBEq for IntType
deriving instance ReflBEq, LawfulBEq for Mutability

-- Structural `BEq` for `Ty`, defined mutually with the `List Ty`
-- case so the recursion is non-`partial`. The `deriving BEq`
-- handler emits a `partial def` for nested inductives, which
-- blocks any `LawfulBEq` proof; this version is unfoldable
-- and lets `LawfulBEq Ty` go through. Wrapped in `defRaw after`
-- so the generated module gets the same instance.
mutual
def Ty.beq : Ty → Ty → Bool
  | .bool, .bool => true
  | .int it₁, .int it₂ => it₁ == it₂
  | .param i₁, .param i₂ => i₁ == i₂
  | .alias b₁ n₁ a₁, .alias b₂ n₂ a₂ =>
      Ty.beq b₁ b₂ && n₁ == n₂ && Ty.beqList a₁ a₂
  | .ctor n₁ a₁, .ctor n₂ a₂ =>
      n₁ == n₂ && Ty.beqList a₁ a₂
  | .ref r₁ m₁ p₁, .ref r₂ m₂ p₂ =>
      r₁ == r₂ && m₁ == m₂ && Ty.beq p₁ p₂
  | .box i₁, .box i₂ => Ty.beq i₁ i₂
  | .array e₁ n₁, .array e₂ n₂ => Ty.beq e₁ e₂ && n₁ == n₂
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | x :: xs, y :: ys => Ty.beq x y && Ty.beqList xs ys
  | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

mutual
private theorem Ty.beq_self : ∀ (t : Ty), Ty.beq t t = true
  | .bool => rfl
  | .int _ | .param _ => by simp [Ty.beq]
  | .alias b _ args => by simp [Ty.beq, Ty.beq_self b, Ty.beqList_self args]
  | .ctor _ args => by simp [Ty.beq, Ty.beqList_self args]
  | .ref _ _ p => by simp [Ty.beq, Ty.beq_self p]
  | .box i => by simp [Ty.beq, Ty.beq_self i]
  | .array e _ => by simp [Ty.beq, Ty.beq_self e]

private theorem Ty.beqList_self : ∀ (ts : List Ty), Ty.beqList ts ts = true
  | [] => rfl
  | x :: xs => by simp [Ty.beqList, Ty.beq_self x, Ty.beqList_self xs]
end

mutual
private theorem Ty.eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b
  | .bool, .bool, _ => rfl
  | .int _, .int _, h | .param _, .param _, h => by
      simp [Ty.beq] at h; exact congrArg _ h
  | .alias _ _ _, .alias _ _ _, h => by
      simp [Ty.beq] at h
      obtain ⟨⟨hbb, rfl⟩, ha⟩ := h
      cases Ty.eq_of_beq hbb; cases Ty.eq_of_beqList ha; rfl
  | .ctor _ _, .ctor _ _, h => by
      simp [Ty.beq] at h
      obtain ⟨rfl, ha⟩ := h
      cases Ty.eq_of_beqList ha; rfl
  | .ref _ _ _, .ref _ _ _, h => by
      simp [Ty.beq] at h
      obtain ⟨⟨rfl, rfl⟩, hpb⟩ := h
      cases Ty.eq_of_beq hpb; rfl
  | .box _, .box _, h => by
      simp [Ty.beq] at h; exact congrArg _ (Ty.eq_of_beq h)
  | .array _ _, .array _ _, h => by
      simp [Ty.beq] at h
      obtain ⟨heb, rfl⟩ := h
      cases Ty.eq_of_beq heb; rfl

private theorem Ty.eq_of_beqList : ∀ {a b : List Ty}, Ty.beqList a b = true → a = b
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
      simp [Ty.beqList] at h
      cases Ty.eq_of_beq h.1; cases Ty.eq_of_beqList h.2; rfl
end

instance : ReflBEq Ty where rfl := Ty.beq_self _
instance : LawfulBEq Ty where eq_of_beq := Ty.eq_of_beq
}

defEnum IntValue (.raw "iv", .cal (.raw "IV"))
  "Integer Values"
  (.plain "A concrete runtime integer value, carrying both \
   its width and its payload.")
where
  | u8 (val : UInt8)
    "An 8-bit unsigned integer."
    (mathdoc! "#u8 n")
  | u16 (val : UInt16)
    "A 16-bit unsigned integer."
    (mathdoc! "#u16 n")
  | u32 (val : UInt32)
    "A 32-bit unsigned integer."
    (mathdoc! "#u32 n")
  | u64 (val : UInt64)
    "A 64-bit unsigned integer."
    (mathdoc! "#u64 n")
  | usize (val : USize)
    "A pointer-sized unsigned integer."
    (mathdoc! "#usize n")
  deriving Repr, BEq, Hashable


/-- A generalized type is either a type or a region.

    From `definitions/functions.md`:
    "A generalized type is either a type τ or a region r" -/
inductive GenTy where
  | ty (τ : Ty)
  | region (r : Region)
  deriving Repr, BEq, Hashable

/-- A single constraint in a parameter environment.

    From `definitions/functions.md`:
    - `regionOutlives r r'`: region `r` outlives region `r'`
    - `tyOutlives τ r`: all regions in `τ` outlive `r`
    - `tyImplsTrait τ Tr`: type `τ` implements trait `Tr` -/
inductive Constraint where
  | regionOutlives (r₁ r₂ : Region)
  | tyOutlives (τ : Ty) (r : Region)
  | tyImplsTrait (τ : Ty) (traitName : String)
  deriving Repr, BEq, Hashable

/-- A parameter environment: a list of constraints.

    From `definitions/functions.md`:
    "A param env E is a list of constraints" -/
abbrev ParamEnv := List Constraint

namespace Ty

defFn bytes (.plain "bytes")
  (doc! "The size of a type in bytes, if known. \
    References and `Box` pointers occupy 8 bytes (the size \
    of an address). Arrays multiply the element size by \
    the length, propagating `None` when the element has \
    unknown size.")
  (τ "The type." : Ty)
  : Option Nat where
  | .bool => Some 1
  | .int it => Some (sizeBytes it↦size)
  | .ref _ _ _ => Some 8
  | .box _ => Some 8
  | .array elem n =>
      let sz ← bytes elem ;
      Some (sz * n)
  | _ => None

defFn regions (.plain "regions")
  (.plain "Regions occurring directly in a type.")
  (τ "The type to extract regions from." : Ty)
  : List Region where
  | .bool => []
  | .int _ => []
  | .param _ => []
  | .alias base _ args =>
      base·regions ++ (args·flatMap fun a => a·regions)
  | .ctor _ args => args·flatMap fun a => a·regions
  | .ref r _ pointee => r :: pointee·regions
  | .box inner => inner·regions
  | .array elem _ => elem·regions

/-- `Contains fields τ τ'` holds when `τ` contains `τ'`.

    From `definitions.md`:
    1. `τ = τ'`, or
    2. `τ` is an ADT containing a field `f : τ_f` and `τ_f` contains `τ'`
    3. `τ = &'r mut τ'` and `τ_tgt` contains `τ'`

    Since we do not have access to ADT field information at the type level,
    case 2 is modelled via the `fields` parameter, which supplies the
    field types for each type-constructor name.

    Expressed as an inductive proposition to avoid termination issues
    (the `fields` function can produce arbitrary types). -/
inductive Contains (fields : TyCtorName → List Ty) : Ty → Ty → Prop where
  | refl {τ : Ty} : Contains fields τ τ
  | field {name : TyCtorName} {args : List Ty} {τ_f τ' : Ty} :
      τ_f ∈ fields name →
      Contains fields τ_f τ' →
      Contains fields (.ctor name args) τ'
  | deref {r : Region} {pointee τ' : Ty} :
      Contains fields pointee τ' →
      Contains fields (.ref r .mutable pointee) τ'
  | unbox {inner τ' : Ty} :
      Contains fields inner τ' →
      Contains fields (.box inner) τ'
  | arrayElem {elem τ' : Ty} {len : Nat} :
      Contains fields elem τ' →
      Contains fields (.array elem len) τ'

/-- `ContainsRegion fields τ r` holds when `τ` contains lifetime `r`.

    From `definitions.md`:
    "A type τ contains a lifetime r iff τ contains the type `&'r mut τ'`
    for some type τ'." -/
def ContainsRegion (fields : TyCtorName → List Ty) (τ : Ty) (r : Region)
    : Prop :=
  ∃ pointee : Ty, Contains fields τ (.ref r .mutable pointee)

/-- `RegionNested fields τ r` holds when `τ` contains `&'r mut τ'` and
    `τ'` also contains `r`.

    From `definitions.md`:
    "A lifetime r is nested in a type τ iff τ contains a type
    `&'r mut τ'` and `τ'` contains r." -/
def RegionNested (fields : TyCtorName → List Ty) (τ : Ty) (r : Region)
    : Prop :=
  ∃ pointee : Ty,
    Contains fields τ (.ref r .mutable pointee) ∧
    ContainsRegion fields pointee r

/-- The corresponding region of `r` (occurring in `τ`) within `τ_c`.

    From `definitions/types.md`:
    - If `τ = &r m τ'` and `τ_c = &r_c' m τ_c'`, then the
      corresponding region is `r_c'`.
    - If `τ = T⟨τ₁,…,τₙ⟩` and `τ_c = T⟨τ_c₁,…,τ_cₙ⟩`, iterate
      over arguments to find the corresponding region. -/
def correspondingRegion : Ty → Region → Ty → Option Region
  | .ref r _ pointee, target, .ref r_c _ pointee_c =>
    if r == target then some r_c
    else correspondingRegion pointee target pointee_c
  | .box inner, target, .box inner_c =>
    correspondingRegion inner target inner_c
  | .array elem _ , target, .array elem_c _ =>
    correspondingRegion elem target elem_c
  | .ctor name args, target, .ctor name_c args_c =>
    if name == name_c then
      findCorresponding args target args_c
    else
      none
  | _, _, _ => none
where
  findCorresponding : List Ty → Region → List Ty → Option Region
    | [], _, _ => none
    | _ , _, [] => none
    | τ :: τs, target, τ_c :: τ_cs =>
      match correspondingRegion τ target τ_c with
      | some r => some r
      | none => findCorresponding τs target τ_cs

end Ty

namespace ParamEnv

/-- The base outlives relation `E ⊢₀ gτ : r`.

    From `definitions/functions.md`:
    1. Direct: `(gτ : r) ∈ E`
    2. Reflexivity: `E ⊢₀ r : r`
    3. Transitivity: `E ⊢₀ gτ : r` and `E ⊢₀ r : r'` implies
       `E ⊢₀ gτ : r'`

    This is the transitive closure of the region-outlives and
    type-outlives facts in `E`. -/
inductive BaseOutlives : ParamEnv → GenTy → Region → Prop where
  | direct {E : ParamEnv} {r₁ r₂ : Region} :
      .regionOutlives r₁ r₂ ∈ E →
      BaseOutlives E (.region r₁) r₂
  | directTy {E : ParamEnv} {τ : Ty} {r : Region} :
      .tyOutlives τ r ∈ E →
      BaseOutlives E (.ty τ) r
  | refl {E : ParamEnv} {r : Region} :
      BaseOutlives E (.region r) r
  | trans {E : ParamEnv} {gτ : GenTy} {r r' : Region} :
      BaseOutlives E gτ r →
      BaseOutlives E (.region r) r' →
      BaseOutlives E gτ r'

end ParamEnv
