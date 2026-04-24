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

/-- Pointwise union of two maps from keys to sets: for keys
    present in both maps, the values are combined with
    `Std.HashSet.union`. -/
def mapUnionSets {κ α : Type} [BEq κ] [Hashable κ]
    [BEq α] [Hashable α]
    (m₁ m₂ : Map κ (Std.HashSet α)) : Map κ (Std.HashSet α) :=
  m₂.fold (fun acc k v =>
    match acc.get? k with
    | some v' => acc.insert k (v'.union v)
    | none => acc.insert k v) m₁

/-- Merge two maps, combining the values of shared keys with
    `f`. Keys present in only one map are kept with their
    existing value. -/
def mapMergeWith {κ ν : Type} [BEq κ] [Hashable κ]
    (f : ν → ν → ν) (m₁ m₂ : Map κ ν) : Map κ ν :=
  m₂.fold (fun acc k v =>
    match acc.get? k with
    | some v' => acc.insert k (f v' v)
    | none => acc.insert k v) m₁
