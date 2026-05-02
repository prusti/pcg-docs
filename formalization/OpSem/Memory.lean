import OpSem.Pointer
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw

defStruct Memory (.cal (.raw "M"), .text "Mem")
  "Memory"
  (doc! "A memory $\\mathcal\{M} ∈ _Mem_$ is a list of allocations.")
where
  | allocs "The allocations." : List Allocation

/-! Five short-name aliases for `List` operations sit at
    top level in the generated module so DSL-rendered code
    emits the unqualified names directly; we declare them
    here as `defRaw` blocks so the source-side build
    elaborates the same definitions (no mid-file `open`
    needed to find them). The trailing `open AbstractByte`
    keeps the variant names of `AbstractByte` unqualified
    in the rest of the generated file. -/

defRaw before => def last := @List.getLast?
defRaw before => def replicate := @List.replicate
defRaw before => def listSet := @List.set
defRaw before => def listTake := @List.take
defRaw before => def listDrop := @List.drop
defRaw before => open AbstractByte

namespace Memory

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
  : Memory × AllocId :=
    let addr := top ‹m› ;
    let id := AllocId⟨m↦allocs·length⟩ ;
    let alloc := Allocation⟨id, replicate ‹size, uninit›, addr, true⟩ ;
    ⟨Memory⟨m↦allocs ++ [alloc]⟩, id⟩

defProperty validAllocId (.plain "validAllocId")
  short
    (doc! "{id} is a valid allocation id in {m}")
  long
    (doc! "the index of {id} is less than the number of \
      allocations in {m}")
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  := id↦index < m↦allocs·length

open Allocation in
defFn deallocate (.plain "deallocate")
  (.plain "Mark an allocation as dead.")
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  requires validAllocId(m, id)
  : Memory :=
    let alloc := m↦allocs ! id↦index ;
    let dead := Allocation⟨alloc↦id, alloc↦data, alloc↦address, false⟩ ;
    let newAllocs := listSet ‹m↦allocs, id↦index, dead› ;
    Memory⟨newAllocs⟩

open Allocation in

defProperty validMemory (.plain "validMemory")
  short
    (doc! "{m} is a valid memory")
  long
    (doc! "the allocations of {m} are non-overlapping and \
      sorted by address: for every pair of indices i < j, \
      the end address of allocation i is strictly less than \
      the start address of allocation j")
  (m "The memory." : Memory)
  := ∀∀ i, j . i < j < m↦allocs·length → endAddr ‹m↦allocs ! i› < (m↦allocs ! j)↦address

def sub := @Nat.sub

defFn writeBytesAt (.plain "write_bytes_at")
  (.plain "Overwrite a slice of a byte sequence, starting \
    at the given offset, with a new byte sequence.")
  (data "The existing byte sequence." : List AbstractByte)
  (offset "The offset at which to write." : Nat)
  (bytes "The bytes to write." : List AbstractByte)
  : List AbstractByte :=
    listTake ‹offset, data› ++ bytes ++
      listDrop ‹offset + bytes·length, data›

defFn readBytesAt (.plain "read_bytes_at")
  (.plain "Read a byte sub-sequence of a given length from \
    a byte sequence, starting at the given offset.")
  (data "The byte sequence." : List AbstractByte)
  (offset "The offset from which to read." : Nat)
  (len "The number of bytes to read." : Nat)
  : List AbstractByte :=
    listTake ‹len, listDrop ‹offset, data› ›

open Allocation in
defFn checkPtr (.plain "check_ptr")
  (doc! "Check whether a pointer can be dereferenced to access `len` bytes, returning the \
    allocation identifier on success. Returns `None` if the pointer has no provenance, the \
    allocation is dead, or the access is out of bounds.")
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Option (AllocId × Nat) :=
    let prov ← ptr↦provenance ;
    let alloc := m↦allocs ! prov↦id↦index ;
    let offset := ptr↦addr - alloc↦address ;
    match canAccess ‹alloc, ptr, len› with
    | true => Some ⟨prov↦id, offset⟩
    | false => None
    end

open Allocation in
defFn store (.plain "store")
  (doc! "Store a byte sequence into memory at the given \
    pointer. If the pointer does not point to a live, \
    in-bounds allocation, the memory is returned unchanged. \
    Behaviour is based on the logic defined \
    {Doc.link (.plain "here") "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations"}.")
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
  (doc! "Load a byte sequence of length `len` from memory at \
    the given pointer. If the pointer does not point to a \
    live, in-bounds allocation, the empty list is returned. \
    Behaviour is based on the logic defined \
    {Doc.link (.plain "here") "https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations"}.")
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
