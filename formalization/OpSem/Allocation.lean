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
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct Allocation (.raw "\\alpha",
    .doc (.plain "Allocation"))
  "Allocations"
  "An allocation {def} in the memory model."
  note "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md"
where
  | id "The allocation identifier." : AllocId
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

def last := @List.getLast?
def replicate := @List.replicate
def listSet := @List.set

open Allocation in
defFn top (.plain "top")
  "The next available address after all allocations."
  (m "The memory." : Memory)
  : Address :=
  match last ‹m↦allocs› with
  | .none => Address⟨0⟩
  | .some alloc => Address⟨endAddr ‹alloc› + 1⟩
  end

open Allocation AbstractByte in
defFn allocate (.plain "allocate")
  "Allocate a new block of memory, returning the \
   updated memory and the new allocation's identifier."
  (m "The memory." : Memory)
  (size "The size in bytes." : Nat)
  : Memory × AllocId begin
  let addr := top ‹m›
  let id := AllocId⟨m↦allocs·length⟩
  let alloc := Allocation⟨id, replicate ‹size, uninit›, addr, true⟩
  return ⟨Memory⟨m↦allocs ++ [alloc]⟩, id⟩

defProperty validAllocId (.plain "validAllocId")
  "The allocation identifier is in range."
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  latex
    (.seq [.plain "An allocation identifier is ",
           .italic (.plain "valid"),
           .plain " for a memory iff its index is less than the number of allocations."])
  := id↦index < m↦allocs·length

open Allocation in
defFn deallocate (.plain "deallocate")
  "Mark an allocation as dead."
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  requires validAllocId(m, id)
  : Memory begin
  let alloc := m↦allocs ! id↦index
  let dead := Allocation⟨alloc↦id, alloc↦data, alloc↦address, false⟩
  let newAllocs := listSet ‹m↦allocs, id↦index, dead›
  return Memory⟨newAllocs⟩

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
