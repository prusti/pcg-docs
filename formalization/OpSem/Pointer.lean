import OpSem.Allocation

defStruct Provenance (.raw "\\pi", .doc (.plain "Provenance"))
  "Provenances"
  "A pointer provenance {def}, identifying the allocation."
where
  | id "The allocation identifier." : AllocId
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct ThinPointer (.raw "ptr", .doc (.plain "ThinPointer"))
  "Thin Pointers"
  "A thin pointer {def}: an address together with optional provenance."
where
  | addr "The address." : Address
  | provenance "The optional provenance." : Option Provenance
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct Pointer (.raw "\\hat{p}", .doc (.plain "Pointer"))
  "Pointers"
  "A pointer {def}, represented as a wrapper around a thin pointer."
where
  | thin "The underlying thin pointer." : ThinPointer
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Allocation

defFn canAccess (.plain "can_access")
  (.seq [.plain "Whether the allocation is live and can \
    be accessed at the given pointer for ", .code "len",
    .plain " bytes."])
  (alloc "The allocation." : Allocation)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Bool :=
    alloc↦live
      ∧ alloc↦address ≤ ptr↦addr
      ∧ ptr↦addr + len ≤ endAddr ‹alloc›

end Allocation

