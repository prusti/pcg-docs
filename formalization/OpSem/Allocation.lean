import OpSem.Address
import OpSem.AbstractByte
import Core.Dsl.DefFn

defStruct Allocation (.raw "\\alpha",
    .doc (.plain "Allocation"))
  "Allocations"
  "An allocation {def} in the memory model."
  note "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md"
where
  | data "The byte contents." : List AbstractByte
  | address "The base address." : Address
  | live "Whether the allocation is live." : Bool

namespace Allocation

defFn overlaps (.plain "overlaps")
  "Whether an address falls within the allocation."
  (alloc "The allocation." : Allocation)
  (a "The address." : Address)
  : Bool := alloc↦address↦addr < a↦addr ∧ a↦addr < alloc↦address↦addr + alloc↦data·length

end Allocation

defStruct Memory (.cal (.raw "M"), .doc (.plain "Mem"))
  "Memory"
  "A memory {def} is a list of allocations."
where
  | allocations "The allocations." : List Allocation
