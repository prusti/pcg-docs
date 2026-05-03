import Std.Data.HashMap
import Std.Data.HashSet

/-- A map backed by `Std.HashMap`.
    In generated Rust code this becomes `HashMap<K, V>`. -/
abbrev Map (κ : Type) [BEq κ] [Hashable κ] (ν : Type) :=
  Std.HashMap κ ν

/-- Look up a key in a `Map`. -/
def mapGet {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) : Option ν :=
  m.get? k

/-- Look up a key in a `Map`, panicking when absent. The
    caller is responsible for upholding a precondition that
    guarantees `k` is present (typically a `defProperty`
    discharged via the `requires` clause). -/
def mapAt {κ : Type} [BEq κ] [Hashable κ]
    {ν : Type} [Inhabited ν]
    (m : Map κ ν) (k : κ) : ν :=
  m.get! k

/-- Insert or overwrite a key/value pair in a `Map`. -/
def mapInsert {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) (v : ν) : Map κ ν :=
  m.insert k v

/-- Remove a key (and its value) from a `Map`. Returns
    the map unchanged if the key is absent. -/
def mapRemove {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) : Map κ ν :=
  m.erase k

/-- The empty map. -/
def mapEmpty {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    : Map κ ν :=
  ∅

/-- A map with a single entry `k ↦ v`. -/
def mapSingleton {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (k : κ) (v : ν) : Map κ ν :=
  (∅ : Std.HashMap κ ν).insert k v

/-- Merge two maps, combining the values of shared keys with
    `f`. Keys present in only one map are kept with their
    existing value. -/
def mapMergeWith {κ ν : Type} [BEq κ] [Hashable κ]
    (f : ν → ν → ν) (m₁ m₂ : Map κ ν) : Map κ ν :=
  m₂.fold (fun acc k v =>
    match acc.get? k with
    | some v' => acc.insert k (f v' v)
    | none => acc.insert k v) m₁

/-- Pointwise union of two maps from keys to sets: for keys
    present in both maps, the values are combined with
    `Std.HashSet.union`. -/
def mapUnionSets {κ α : Type} [BEq κ] [Hashable κ]
    [BEq α] [Hashable α]
    (m₁ m₂ : Map κ (Std.HashSet α)) : Map κ (Std.HashSet α) :=
  mapMergeWith Std.HashSet.union m₁ m₂

/-- The values of a `Map`, in unspecified order. Useful for
    iterating every entry of a map without caring about the
    keys. -/
def mapValues {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) : List ν :=
  m.fold (fun acc _ v => v :: acc) []

private theorem List.mem_foldlConsSnd_of_mem
    {α β : Type} (l : List (α × β)) {init : List β} {b : β}
    (h : b ∈ init) :
    b ∈ l.foldl (fun acc x => x.2 :: acc) init := by
  induction l generalizing init with
  | nil => exact h
  | cons _ _ ih => exact ih (List.mem_cons_of_mem _ h)

private theorem List.mem_foldlConsSnd_of_pair_mem
    {α β : Type} (l : List (α × β)) {init : List β}
    {a : α} {b : β} (h : (a, b) ∈ l) :
    b ∈ l.foldl (fun acc x => x.2 :: acc) init := by
  induction l generalizing init with
  | nil => exact (List.not_mem_nil h).elim
  | cons x xs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_foldlConsSnd_of_mem xs
          (List.mem_cons_self)
      · exact ih h

/-- If `mapGet m k = some v` then `v` appears in `mapValues m`.
    The implementation goes through `Std.HashMap.toList` and a
    list-fold lemma; we expose it here so call sites can lift
    `forAll`-style preconditions over a map's values to a fact
    about a particular looked-up value. -/
theorem mem_mapValues_of_mapGet_eq_some
    {κ : Type} [BEq κ] [EquivBEq κ] [Hashable κ]
    [LawfulHashable κ] {ν : Type}
    {m : Map κ ν} {k : κ} {v : ν}
    (h : mapGet m k = some v) : v ∈ mapValues m := by
  obtain ⟨k', _, hmem⟩ :=
    Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp h
  unfold mapValues
  rw [Std.HashMap.fold_eq_foldl_toList]
  exact List.mem_foldlConsSnd_of_pair_mem _ hmem

private theorem List.mem_foldlConsSnd_iff
    {α β : Type} (l : List (α × β)) (init : List β) (b : β) :
    b ∈ l.foldl (fun acc x => x.2 :: acc) init ↔
    b ∈ init ∨ ∃ a, (a, b) ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨xa, xb⟩ := x
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, ha⟩)
      · rcases h with rfl | h
        · exact Or.inr ⟨xa, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inl h
      · exact Or.inr ⟨a, Or.inr ha⟩
    · rintro (h | ⟨a, ⟨_, rfl⟩ | ha⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨a, ha⟩

/-- The values of `mapInsert m k v` are exactly `v` together
    with the values of `m` minus the one at key `k` (if any).
    Stated weakly: every element of `mapValues (mapInsert m k v)`
    is either `v` itself or appeared in `mapValues m`. -/
theorem mem_mapValues_mapInsert
    {κ : Type} [BEq κ] [EquivBEq κ] [Hashable κ]
    [LawfulHashable κ] {ν : Type}
    {m : Map κ ν} {k : κ} {v e : ν}
    (h : e ∈ mapValues (mapInsert m k v)) :
    e = v ∨ e ∈ mapValues m := by
  unfold mapValues mapInsert at *
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  rcases (List.mem_foldlConsSnd_iff _ _ _).mp h with hinit | ⟨a, hpair⟩
  · cases hinit
  · -- (a, e) ∈ (m.insert k v).toList
    -- via toList_insert_perm: (a, e) ∈ ⟨k, v⟩ :: m.toList.filter (¬k == ·.1)
    have hperm := Std.HashMap.toList_insert_perm (m := m) (k := k) (v := v)
    have hmem : (a, e) ∈ (⟨k, v⟩ :: m.toList.filter (fun p => ¬k == p.1)) :=
      hperm.mem_iff.mp hpair
    rcases List.mem_cons.mp hmem with heq | hfilt
    · left
      have : (a, e) = (k, v) := heq
      exact (Prod.mk.injEq .. |>.mp this).2
    · right
      have hmem' : (a, e) ∈ m.toList :=
        (List.mem_filter.mp hfilt).1
      rw [Std.HashMap.fold_eq_foldl_toList]
      exact List.mem_foldlConsSnd_of_pair_mem _ hmem'
