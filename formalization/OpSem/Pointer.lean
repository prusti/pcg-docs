import OpSem.Allocation

defStruct Provenance (.raw "\\pi", .doc (.plain "Provenance"))
  "Provenances"
  "A pointer provenance {def}, identifying the allocation."
where
  | id "The allocation identifier." : AllocId
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct ThinPointer (.raw "p", .doc (.plain "ThinPointer"))
  "Thin Pointers"
  "A thin pointer {def}: an address together with optional provenance."
where
  | addr "The address." : Address
  | provenance "The optional provenance." : Option Provenance
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Allocation

defFn canAccess (.plain "can_access")
  "Whether the allocation is live and can be accessed at \
   the given pointer for `len` bytes."
  (alloc "The allocation." : Allocation)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Bool :=
    alloc↦live
      ∧ alloc↦address ≤ ptr↦addr
      ∧ ptr↦addr + len ≤ endAddr ‹alloc›

end Allocation

namespace Memory

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
  "Check whether a pointer can be dereferenced to access `len` bytes, \
   returning the allocation identifier on success. \
   Returns `None` if the pointer has no provenance, the allocation is dead, \
   or the access is out of bounds."
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
  "Store a byte sequence into memory at the given pointer. \
   If the pointer does not point to a live, in-bounds allocation, \
   the memory is returned unchanged. \
   Behaviour is based on the logic defined here: \
   https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations"
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
  "Load a byte sequence of length `len` from memory at the given pointer. \
   If the pointer does not point to a live, in-bounds allocation, \
   the empty list is returned. \
   Behaviour is based on the logic defined here: \
   https://github.com/minirust/minirust/blob/master/spec/mem/basic.md#operations"
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
