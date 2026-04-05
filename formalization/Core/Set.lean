import Std.Data.HashSet

/-- A set backed by `Std.HashSet`.
    In generated Rust code this becomes `HashSet<T>`. -/
abbrev Set (α : Type) [BEq α] [Hashable α] :=
  Std.HashSet α

namespace Set

/-- Singleton set. -/
def singleton {α : Type} [BEq α] [Hashable α]
    (a : α) : Set α :=
  (∅ : Std.HashSet α).insert a

/-- Set union. -/
def union {α : Type} [BEq α] [Hashable α]
    (s₁ s₂ : Set α) : Set α :=
  Std.HashSet.union s₁ s₂

instance (α : Type) [BEq α] [Hashable α]
    : Append (Set α) := ⟨union⟩

/-- Convert an `Option` to a set. -/
def ofOption {α : Type} [BEq α] [Hashable α]
    : Option α → Set α
  | some a => singleton a
  | none => ∅

/-- Flat-map over a list, collecting results
    into a set. -/
def flatMapList {α : Type} {β : Type}
    [BEq β] [Hashable β]
    (l : List α) (f : α → Set β) : Set β :=
  l.foldl (fun (acc : Std.HashSet β) x =>
    Std.HashSet.union acc (f x)) ∅

end Set

namespace Option

/-- Convert an option to a `Set`. -/
def toSet {α : Type} [BEq α] [Hashable α]
    (o : Option α) : Set α :=
  Set.ofOption o

end Option
