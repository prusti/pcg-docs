import OpSem.Address
import OpSem.AbstractByte
import Core.Dsl.DefFn

defStruct AllocId (.raw "id", .text "AllocId")
  "Allocation Identifiers"
  (.seq [.plain "An allocation identifier ",
    .math (.seq [.raw "id", .sym .setContains, .text "AllocId"]),
    .plain "."])
  constructor "AllocId"
  link "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#data-structures"
where
  | index "The allocation index." : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct Allocation (.raw "\\alpha",
    .text "Allocation")
  "Allocations"
  (.seq [.plain "An allocation ",
    .math (.seq [.raw "\\alpha", .sym .setContains, .text "Allocation"]),
    .plain " in the memory model."])
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

defFn nonOverlapping (.plain "nonOverlapping")
  (doc! "Whether two allocations occupy disjoint address ranges: one's end address is at or before \
    the other's start address. Symmetric in its arguments. An allocation is never non-overlapping \
    with itself (unless it has zero bytes), since each allocation's address range overlaps fully \
    with itself.")
  (a "The first allocation." : Allocation)
  (b "The second allocation." : Allocation)
  : Bool :=
    endAddr ‹a› ≤ b↦address ∨ endAddr ‹b› ≤ a↦address

end Allocation

