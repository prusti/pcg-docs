import Core.Dsl.DefStruct

defStruct Address (.raw "a", .cal (.raw "A"))
  "Addresses"
  (.seq [.plain "A memory address ",
    Doc.defMath (.raw "a") (.cal (.raw "A")), .plain "."])
  constructor "Address"
where
  | addr "The address value." : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

instance : Ord Address where
  compare a b := compare a.addr b.addr

instance : LE Address where
  le a b := a.addr ≤ b.addr

instance : LT Address where
  lt a b := a.addr < b.addr

instance (a b : Address) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.addr ≤ b.addr))

instance (a b : Address) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.addr < b.addr))

instance : HSub Address Address Nat where
  hSub a b := a.addr - b.addr

instance : HAdd Address Nat Address where
  hAdd a n := ⟨a.addr + n⟩
