import OpSem.Address
import OpSem.AbstractByte
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct AllocId (.raw "id", .doc (.plain "AllocId"))
  "Allocation Identifiers"
  "An allocation identifier {def}."
  constructor "AllocId"
  note "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#data-structures"
where
  | index "The allocation index." : Nat

defStruct Allocation (.raw "\\alpha",
    .doc (.plain "Allocation"))
  "Allocations"
  "An allocation {def} in the memory model."
  note "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md"
where
  | data "The byte contents." : List AbstractByte
  | address "The base address." : Address
  | live "Whether the allocation is live." : Bool
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Allocation

defFn endAddr (.plain "end")
  "The end address of an allocation."
  (alloc "The allocation." : Allocation)
  : Nat := alloc↦address↦addr + alloc↦data·length

defFn overlaps (.plain "overlaps")
  "Whether an address falls within the allocation."
  (alloc "The allocation." : Allocation)
  (a "The address." : Address)
  : Bool := alloc↦address↦addr < a↦addr ∧ a↦addr ≤ endAddr ‹alloc›

end Allocation

defStruct Memory (.cal (.raw "M"), .doc (.plain "Mem"))
  "Memory"
  "A memory {def} is a list of allocations."
where
  | allocs "The allocations." : List Allocation

namespace Memory
open Allocation in

defProperty validMemory (.plain "validMemory")
  "Allocations are ordered and non-overlapping."
  (m "The memory." : Memory)
  latex
    (.seq [.plain "A memory is ",
           .italic (.plain "valid"),
           .plain " iff for all ",
           .math (.raw "i < j < |allocations|"),
           .plain ", ",
           .math (.raw "\\text{endAddr}(allocations[i]) < allocations[j].address.addr"),
           .plain "."])
  := ∀∀ i, ∀∀ j, i < j < m↦allocs·length → endAddr ‹m↦allocs ! i› < (m↦allocs ! j)↦address↦addr

end Memory
