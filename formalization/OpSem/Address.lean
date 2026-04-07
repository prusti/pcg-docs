import Core.Dsl.DefStruct

defStruct Address (.raw "a", .cal (.raw "A"))
  "Addresses"
  "A memory address {def}."
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
