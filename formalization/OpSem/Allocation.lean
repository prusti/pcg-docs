import OpSem.Address
import OpSem.AbstractByte
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct AllocId (.raw "id", .doc (.plain "AllocId"))
  "Allocation Identifiers"
  "An allocation identifier {def}."
  constructor "AllocId"
  link "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#data-structures"
where
  | index "The allocation index." : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct Allocation (.raw "\\alpha",
    .doc (.plain "Allocation"))
  "Allocations"
  "An allocation {def} in the memory model."
  link "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md"
where
  | id "The allocation identifier." : AllocId
  | data "The byte contents." : List AbstractByte
  | address "The base address." : Address
  | live "Whether the allocation is live." : Bool
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Allocation

defFn endAddr (.plain "end")
  (.plain "The end address of an allocation.")
  (alloc "The allocation." : Allocation)
  : Address := Address⟨alloc↦address↦addr + alloc↦data·length⟩

defFn overlaps (.plain "overlaps")
  (.plain "Whether an address falls within the allocation.")
  (alloc "The allocation." : Allocation)
  (a "The address." : Address)
  : Bool := alloc↦address < a ≤ endAddr ‹alloc›

end Allocation

