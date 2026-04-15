import OpSem.Pointer
import Core.Dsl.DefProperty

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
  (.plain "The next available address after all allocations.")
  (m "The memory." : Memory)
  : Address :=
  match last ‹m↦allocs› with
  | .none => Address⟨0⟩
  | .some alloc => Address⟨(endAddr ‹alloc›)↦addr + 1⟩
  end

open Allocation AbstractByte in
defFn allocate (.plain "allocate")
  (.plain "Allocate a new block of memory, returning the \
   updated memory and the new allocation's identifier.")
  (m "The memory." : Memory)
  (size "The size in bytes." : Nat)
  : Memory × AllocId begin
  let addr := top ‹m›
  let id := AllocId⟨m↦allocs·length⟩
  let alloc := Allocation⟨id, replicate ‹size, uninit›, addr, true⟩
  return ⟨Memory⟨m↦allocs ++ [alloc]⟩, id⟩

defProperty validAllocId (.plain "validAllocId")
  (mDoc, idDoc) =>
    (.seq [idDoc, .plain " is a valid allocation id in ",
           mDoc])
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  := id↦index < m↦allocs·length

open Allocation in
defFn deallocate (.plain "deallocate")
  (.plain "Mark an allocation as dead.")
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
  (mDoc) =>
    (.seq [mDoc, .plain " is a valid memory"])
  (m "The memory." : Memory)
  := ∀∀ i, ∀∀ j, i < j < m↦allocs·length → endAddr ‹m↦allocs ! i› < (m↦allocs ! j)↦address

def sub := @Nat.sub

def writeBytesAt
    (data : List AbstractByte) (offset : Nat)
    (bytes : List AbstractByte) : List AbstractByte :=
  data.take offset ++ bytes ++ data.drop (offset + bytes.length)

def readBytesAt
    (data : List AbstractByte) (offset : Nat) (len : Nat)
    : List AbstractByte :=
  (data.drop offset).take len

open Allocation in
defFn checkPtr (.plain "check_ptr")
  (.seq [.plain "Check whether a pointer can be \
    dereferenced to access ", .code "len",
    .plain " bytes, returning the allocation identifier \
    on success. Returns ", .code "None", .plain " if the \
    pointer has no provenance, the allocation is dead, \
    or the access is out of bounds."])
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Option (AllocId × Nat) begin
  let prov ← ptr↦provenance
  let alloc := m↦allocs ! prov↦id↦index
  let offset := ptr↦addr - alloc↦address
  return match canAccess ‹alloc, ptr, len› with
  | true => Some ⟨prov↦id, offset⟩
  | false => None
  end

open Allocation in
defFn store (.plain "store")
  (.seq [.plain "Store a byte sequence into memory at \
    the given pointer. If the pointer does not point to \
    a live, in-bounds allocation, the memory is returned \
    unchanged. Behaviour is based on the logic defined ",
    .link (.plain "here")
      "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations",
    .plain "."])
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (bytes "The bytes to store." : List AbstractByte)
  : Memory :=
    match checkPtr ‹m, ptr, bytes·length› with
    | .none => m
    | .some ⟨aid, offset⟩ =>
        let alloc := m↦allocs ! aid↦index ;
        let newData := writeBytesAt ‹alloc↦data, offset, bytes› ;
        let newAlloc := Allocation⟨alloc↦id, newData, alloc↦address, alloc↦live⟩ ;
        let newAllocs := listSet ‹m↦allocs, aid↦index, newAlloc› ;
        Memory⟨newAllocs⟩
    end

open Allocation in
defFn load (.plain "load")
  (.seq [.plain "Load a byte sequence of length ",
    .code "len", .plain " from memory at the given \
    pointer. If the pointer does not point to a live, \
    in-bounds allocation, the empty list is returned. \
    Behaviour is based on the logic defined ",
    .link (.plain "here")
      "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations",
    .plain "."])
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (len "The number of bytes to load." : Nat)
  : List AbstractByte :=
    match checkPtr ‹m, ptr, len› with
    | .none => []
    | .some ⟨aid, offset⟩ =>
        let alloc := m↦allocs ! aid↦index ;
        readBytesAt ‹alloc↦data, offset, len›
    end

end Memory
