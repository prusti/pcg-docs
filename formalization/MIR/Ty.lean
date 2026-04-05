import MIR.Region
import Core.Dsl.DefFn

defStruct TyCtorName (.math (.var "T"))
  "A type constructor name, representing an ADT or \
   primitive type."
where
  | name "The constructor name." : String

defStruct AliasTyName (.math (.var "A"))
  "An associated type name."
where
  | name "The associated type name." : String

defEnum Mutability (.math (.var "m"))
  "Mutability of a reference."
where
  | shared
    "Shared"
    (.doc (.text "shared"))
  | mutable
    "Mutable"
    (.doc (.text "mut"))

defEnum Ty (.math (.var "τ"))
  "A type in the MIR. See definitions/types.md."
where
  | param (index : Nat)
    "A type parameter."
    (.doc (.text "param "),
     #index (.var "i"))
  | alias (base : Ty) (name : AliasTyName)
      (args : List Ty)
    "An alias type."
    (#base, .doc (.text "::"), #name,
     .sym .langle,
     #args (.var "τ̄"),
     .sym .rangle)
  | ctor (name : TyCtorName) (args : List Ty)
    "A type constructor application."
    (#name, .sym .langle,
     #args (.var "τ̄"),
     .sym .rangle)
  | ref (region : Region) (mutability : Mutability)
      (pointee : Ty)
    "A reference type."
    (.doc (.text "&"), #region, .doc (.text " "),
     #mutability, .doc (.text " "), #pointee)
  | box (inner : Ty)
    "A box type."
    (.doc (.code "Box"),
     .sym .langle,
     #inner,
     .sym .rangle)
  | array (elem : Ty) (len : Nat)
    "A fixed-size array type."
    (.doc (.text "["), #elem, .doc (.text "; "),
     #len (.var "n"), .doc (.text "]"))
  deriving Repr, BEq, Hashable

instance : Inhabited Ty where
  default := .param 0

defEnum Value (.math (.var "v"))
  "A concrete runtime value."
where
  | bool (val : Bool)
    "A boolean value."
    (.doc (.text "bool "), #val (.var "b"))
  | u8 (val : UInt8)
    "An 8-bit unsigned integer."
    (.doc (.text "u8 "), #val (.var "n"))
  | u16 (val : UInt16)
    "A 16-bit unsigned integer."
    (.doc (.text "u16 "), #val (.var "n"))
  | u32 (val : UInt32)
    "A 32-bit unsigned integer."
    (.doc (.text "u32 "), #val (.var "n"))
  | u64 (val : UInt64)
    "A 64-bit unsigned integer."
    (.doc (.text "u64 "), #val (.var "n"))
  | usize (val : USize)
    "A pointer-sized unsigned integer."
    (.doc (.text "usize "), #val (.var "n"))
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

defFn regions (.text "regions")
  "Regions occurring directly in a type."
  (τ "The type to extract regions from." : Ty)
  : List Region where
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
