import Core.Dsl.DefStruct
import Core.Dsl.DefRaw

defStruct Address (.raw "a", .cal (.raw "A"))
  "Addresses"
  (.seq [.plain "A memory address ",
    .math (.seq [.raw "a", .sym .setContains, .cal (.raw "A")]), .plain "."])
  constructor "Address"
where
  | addr "The address value." : Nat
  deriving Repr, Hashable, Inhabited

-- `Ord` is source-only — it isn't needed by the generated
-- Lean project (the export uses `BEq`/`Hashable`) but the
-- source still relies on it for `compare`-based operations.
instance : Ord Address where
  compare a b := compare a.addr b.addr

-- The DSL has no `instance` syntax, so the order/arithmetic
-- instances `Address` exposes — and the explicit
-- `DecidableEq` instance the generated structure (which only
-- derives `BEq` etc.) needs — sit in `defRaw` blocks: the
-- inner instances are real Lean (the IDE keeps full
-- highlighting / hover / gotoDef on them) and the export
-- pipeline picks their verbatim source up via the registry.
defRaw after =>
instance : LT Address where
  lt a b := a.addr < b.addr

defRaw after =>
instance : LE Address where
  le a b := a.addr ≤ b.addr

defRaw after =>
instance (a b : Address) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.addr < b.addr))

defRaw after =>
instance (a b : Address) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.addr ≤ b.addr))

defRaw after =>
instance : DecidableEq Address :=
  fun a b => if h : a.addr = b.addr
    then isTrue (by cases a; cases b; simp_all)
    else isFalse (by intro heq; cases heq; exact h rfl)

defRaw after =>
instance : HSub Address Address Nat where
  hSub a b := a.addr - b.addr

defRaw after =>
instance : HAdd Address Nat Address where
  hAdd a n := ⟨a.addr + n⟩
