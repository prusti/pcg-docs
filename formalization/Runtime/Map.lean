import Std.Data.HashMap

/-- A map backed by `Std.HashMap`.
    In generated Rust code this becomes `HashMap<K, V>`. -/
abbrev Map (κ : Type) [BEq κ] [Hashable κ] (ν : Type) :=
  Std.HashMap κ ν

/-- Look up a key in a `Map`. -/
def mapGet {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) : Option ν :=
  m.get? k
