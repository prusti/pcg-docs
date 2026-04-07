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
      ∧ ptr↦addr↦addr + len ≤ (endAddr ‹alloc›)↦addr

end Allocation

namespace Memory

open Allocation in
defFn checkPtr (.plain "check_ptr")
  "Check whether a pointer can be dereferenced to access `len` bytes, \
   returning the allocation identifier on success. \
   Returns `None` if the pointer has no provenance, the allocation is dead, \
   or the access is out of bounds."
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Option AllocId begin
  let prov ← ptr↦provenance
  let alloc := m↦allocs ! prov↦id↦index
  return match canAccess ‹alloc, ptr, len› with
  | true => Some prov↦id
  | false => None
  end

end Memory
