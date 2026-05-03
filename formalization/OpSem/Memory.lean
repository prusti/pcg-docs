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
  match last m↦allocs with
  | .none => Address⟨0⟩
  | .some alloc => Address⟨(endAddr alloc)↦addr + 1⟩
  end

open Allocation AbstractByte in
defFn allocate (.plain "allocate")
  (.plain "Allocate a new block of memory, returning the \
   updated memory and the new allocation's identifier.")
  (m "The memory." : Memory)
  (size "The size in bytes." : Nat)
  : Memory × AllocId :=
    let addr := top m ;
    let id := AllocId⟨m↦allocs·length⟩ ;
    let alloc := Allocation⟨id, replicate size uninit, addr, true⟩ ;
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

defProperty validProvenance (.plain "validProvenance")
  short
    (doc! "{prov} is a valid provenance in {m}")
  long
    (doc! "the allocation id of {prov} is a valid \
      allocation id in {m}")
  (m "The memory." : Memory)
  (prov "The provenance." : Provenance)
  := validAllocId m prov↦id

defProperty validPtr (.plain "validPtr")
  short
    (doc! "{ptr} is a valid pointer in {m}")
  long
    (doc! "if {ptr} carries a provenance, that provenance \
      is valid in {m}")
  (m "The memory." : Memory)
  (ptr "The thin pointer." : ThinPointer)
  where
  | m ; ⟨_, .some prov⟩ => validProvenance m prov
  | _ ; _ => true

open Allocation in
defFn deallocate (.plain "deallocate")
  (.plain "Mark an allocation as dead.")
  (m "The memory." : Memory)
  (id "The allocation identifier." : AllocId)
  requires validAllocId m id
  : Memory :=
    let alloc := m↦allocs ! id↦index ;
    let dead := Allocation⟨alloc↦id, alloc↦data, alloc↦address, false⟩ ;
    let newAllocs := listSet m↦allocs id↦index dead ;
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
  := ∀∀ i, j . i < j < m↦allocs·length → endAddr (m↦allocs ! i) < (m↦allocs ! j)↦address

def sub := @Nat.sub

defFn writeBytesAt (.plain "write_bytes_at")
  (.plain "Overwrite a slice of a byte sequence, starting \
    at the given offset, with a new byte sequence.")
  (data "The existing byte sequence." : List AbstractByte)
  (offset "The offset at which to write." : Nat)
  (bytes "The bytes to write." : List AbstractByte)
  : List AbstractByte :=
    listTake offset data ++ bytes ++
      listDrop (offset + bytes·length) data

defFn readBytesAt (.plain "read_bytes_at")
  (.plain "Read a byte sub-sequence of a given length from \
    a byte sequence, starting at the given offset.")
  (data "The byte sequence." : List AbstractByte)
  (offset "The offset from which to read." : Nat)
  (len "The number of bytes to read." : Nat)
  : List AbstractByte :=
    listTake len (listDrop offset data)

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
    match canAccess alloc ptr len with
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
    match checkPtr m ptr (bytes·length) with
    | .none => m
    | .some ⟨aid, offset⟩ =>
        let alloc := m↦allocs ! aid↦index ;
        let newData := writeBytesAt alloc↦data offset bytes ;
        let newAlloc := Allocation⟨alloc↦id, newData, alloc↦address, alloc↦live⟩ ;
        let newAllocs := listSet m↦allocs aid↦index newAlloc ;
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
    match checkPtr m ptr len with
    | .none => []
    | .some ⟨aid, offset⟩ =>
        let alloc := m↦allocs ! aid↦index ;
        readBytesAt alloc↦data offset len
    end

end Memory

/-! ## Frame-preservation lemmas for `Memory.store`

`Memory.store` writes bytes in-place at an offset inside one
existing allocation and replaces that allocation in the
`allocs` list. The allocation count, every allocation's
`address`, and (under `canAccess`) the overwritten
allocation's `data.length` all survive the update — which
is enough to lift `validMemory` and (in `StackFrame`)
`validStack` through a store. The public lemmas below name
the per-field preservation facts (`store_alloc_*_unchanged`)
and combine them into `store_preserves_validMemory`. Each
declaration sits in its own `defRaw after` block so the
export pipeline copies it verbatim into the generated
project (each `defRaw` carries exactly one Lean command). -/

defRaw after =>
/-- `writeBytesAt` preserves length when the slice fits inside
    the original sequence: `take offset ++ bytes ++ drop
    (offset + bytes.length)` rebuilds a list of the same length
    as `data` whenever `offset + bytes.length ≤ data.length`. -/
private theorem Memory.writeBytesAt_length_eq
    (data : List AbstractByte) (offset : Nat)
    (bytes : List AbstractByte)
    (h : offset + bytes.length ≤ data.length) :
    (writeBytesAt data offset bytes).length = data.length := by
  unfold writeBytesAt listTake listDrop
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

defRaw after =>
/-- From `checkPtr m ptr len = some (aid, offset)` recover the
    `canAccess` predicate on the looked-up allocation: this is
    the only branch of `checkPtr` that returns `some`. -/
private theorem Memory.canAccess_of_checkPtr_eq_some
    {m : Memory} {ptr : ThinPointer} {len : Nat}
    {aid : AllocId} {offset : Nat}
    (h : Memory.checkPtr m ptr len = some (aid, offset)) :
    Allocation.canAccess (m.allocs[aid.index]!) ptr len = true := by
  unfold Memory.checkPtr at h
  cases hprov : ptr.provenance with
  | none => rw [hprov] at h; simp at h
  | some prov =>
    rw [hprov] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i h_can
      injection h with h_eq
      have h_aid : prov.id = aid := by
        have := congrArg Prod.fst h_eq; exact this
      rw [← h_aid]; exact h_can
    · simp at h

defRaw after =>
/-- From `checkPtr m ptr len = some (aid, offset)` recover the
    relation `offset = ptr.addr - alloc.address` between the
    returned offset and the looked-up allocation. -/
private theorem Memory.offset_of_checkPtr_eq_some
    {m : Memory} {ptr : ThinPointer} {len : Nat}
    {aid : AllocId} {offset : Nat}
    (h : Memory.checkPtr m ptr len = some (aid, offset)) :
    (ptr.addr.addr - (m.allocs[aid.index]!).address.addr : Nat) = offset := by
  unfold Memory.checkPtr at h
  cases hprov : ptr.provenance with
  | none => rw [hprov] at h; simp at h
  | some prov =>
    rw [hprov] at h
    simp only [Option.bind_some] at h
    split at h
    · injection h with h_eq
      have h_aid : prov.id = aid := congrArg Prod.fst h_eq
      have h_off_p :
          (ptr.addr - (m.allocs[prov.id.index]!).address : Nat) = offset :=
        congrArg Prod.snd h_eq
      rw [← h_aid]; exact h_off_p
    · simp at h

defRaw after =>
/-- The overwritten allocation produced by `Memory.store` (in
    its `some` branch) keeps the original allocation's
    `address` and `data.length`. The latter rests on
    `canAccess` ensuring `offset + bytes.length ≤
    alloc.data.length`. -/
private theorem Memory.store_overwritten_data_length_eq
    {m : Memory} {ptr : ThinPointer} {bytes : List AbstractByte}
    {aid : AllocId} {offset : Nat}
    (hcp : Memory.checkPtr m ptr bytes.length = some (aid, offset))
    (h_aid : aid.index < m.allocs.length) :
    (writeBytesAt (m.allocs[aid.index]!).data offset bytes).length
      = (m.allocs[aid.index]!).data.length := by
  have h_can := Memory.canAccess_of_checkPtr_eq_some hcp
  unfold Allocation.canAccess at h_can
  simp only [decide_eq_true_eq] at h_can
  obtain ⟨_, h_addr_le, _, h_ptr_plus_le⟩ := h_can
  have h_addr_le' :
      (m.allocs[aid.index]!).address.addr ≤ ptr.addr.addr := h_addr_le
  have h_ptr_plus_le' :
      ptr.addr.addr + bytes.length
        ≤ (Allocation.endAddr (m.allocs[aid.index]!)).addr :=
    h_ptr_plus_le
  unfold Allocation.endAddr at h_ptr_plus_le'
  simp at h_ptr_plus_le'
  -- Bridge `?.getD default` (left over from `unfold endAddr`)
  -- with `[..]!` so omega sees one syntactic form for the
  -- looked-up allocation.
  have h_alloc_eq :
      m.allocs[aid.index]?.getD default = m.allocs[aid.index]! := by
    rw [getElem!_pos m.allocs aid.index h_aid]
    simp [List.getElem?_eq_getElem h_aid]
  rw [h_alloc_eq] at h_ptr_plus_le'
  have h_off_eq := Memory.offset_of_checkPtr_eq_some hcp
  apply Memory.writeBytesAt_length_eq
  omega

defRaw after =>
/-- The shape of the new allocation list produced by
    `Memory.store` in its `some` branch. Centralises the
    repeated `m.allocs.set aid.index { id := …, data :=
    writeBytesAt …, … }` literal and the matching
    `getElem!`-based lookup lemmas. -/
private theorem Memory.store_allocs_set_getElem!
    (m : Memory) (aid : AllocId) (offset : Nat)
    (bytes : List AbstractByte)
    (i : Nat) (h : i < m.allocs.length) :
    let newAlloc : Allocation :=
      { id := (m.allocs[aid.index]!).id,
        data := writeBytesAt (m.allocs[aid.index]!).data offset bytes,
        address := (m.allocs[aid.index]!).address,
        live := (m.allocs[aid.index]!).live }
    (m.allocs.set aid.index newAlloc)[i]!
      = if i = aid.index then newAlloc else m.allocs[i]! := by
  intro newAlloc
  have h_set_len : i < (m.allocs.set aid.index newAlloc).length := by
    simp [List.length_set]; exact h
  rw [getElem!_pos _ i h_set_len]
  by_cases hi : i = aid.index
  · subst hi
    rw [if_pos rfl, List.getElem_set_self]
  · rw [if_neg hi, List.getElem_set_ne (Ne.symm hi), getElem!_pos _ i h]

defRaw after =>
/-- `Memory.store` preserves `endAddr` for every allocation.
    Either branch of `Memory.store` (no-op or in-place
    overwrite at `aid.index`) leaves every allocation's
    `endAddr` alone: the overwritten one keeps its `address`
    and (by `canAccess`) its `data.length`; the others are
    untouched by `List.set`. -/
theorem Memory.store_alloc_endAddr_unchanged
    (m : Memory) (ptr : ThinPointer) (bytes : List AbstractByte)
    (i : Nat) (h : i < m.allocs.length) :
    Allocation.endAddr ((Memory.store m ptr bytes).allocs[i]!)
      = Allocation.endAddr (m.allocs[i]!) := by
  unfold Memory.store
  cases hcp : Memory.checkPtr m ptr bytes.length with
  | none => rfl
  | some p =>
    obtain ⟨aid, offset⟩ := p
    unfold listSet
    rw [Memory.store_allocs_set_getElem! m aid offset bytes i h]
    by_cases hi : i = aid.index
    · -- Overwritten slot: `address` and `data.length` both
      -- match the original allocation.
      subst hi
      simp only [if_true]
      have h_new := Memory.store_overwritten_data_length_eq hcp h
      unfold Allocation.endAddr
      simp only [h_new]
    · simp only [if_neg hi]

defRaw after =>
/-- `Memory.store` preserves the `address` field of every
    existing allocation. Either branch of `Memory.store` (no-op
    or in-place overwrite) leaves the address alone. -/
theorem Memory.store_alloc_address_unchanged
    (m : Memory) (ptr : ThinPointer) (bytes : List AbstractByte)
    (i : Nat) (h : i < m.allocs.length) :
    ((Memory.store m ptr bytes).allocs[i]!).address
      = (m.allocs[i]!).address := by
  unfold Memory.store
  cases hcp : Memory.checkPtr m ptr bytes.length with
  | none => rfl
  | some p =>
    obtain ⟨aid, offset⟩ := p
    unfold listSet
    rw [Memory.store_allocs_set_getElem! m aid offset bytes i h]
    by_cases hi : i = aid.index
    · subst hi; simp only [if_true]
    · simp only [if_neg hi]

defRaw after =>
/-- `Memory.store` preserves the number of allocations: either
    branch leaves the list length alone (`List.set` has the
    same length). -/
theorem Memory.store_allocs_length_unchanged
    (m : Memory) (ptr : ThinPointer) (bytes : List AbstractByte) :
    (Memory.store m ptr bytes).allocs.length = m.allocs.length := by
  unfold Memory.store
  cases hcp : Memory.checkPtr m ptr bytes.length with
  | none => rfl
  | some p =>
    obtain ⟨aid, offset⟩ := p
    unfold listSet; simp

defRaw after =>
/-- `Memory.store` preserves `Memory.validMemory`. The
    overwritten allocation keeps its `address` and (under
    `canAccess`) its `data.length`, so every `endAddr` is
    unchanged and the strict-ordering invariant carries through
    pointwise. -/
theorem Memory.store_preserves_validMemory
    (m : Memory) (ptr : ThinPointer) (bytes : List AbstractByte) :
    Memory.validMemory m → Memory.validMemory (Memory.store m ptr bytes) := by
  intro hvm
  unfold Memory.validMemory at *
  intro i j hpair
  obtain ⟨hij, hjlen⟩ := hpair
  have hjlen' : j < m.allocs.length := by
    rw [Memory.store_allocs_length_unchanged] at hjlen; exact hjlen
  have hilen' : i < m.allocs.length := by omega
  rw [Memory.store_alloc_endAddr_unchanged m ptr bytes i hilen',
      Memory.store_alloc_address_unchanged m ptr bytes j hjlen']
  exact hvm i j ⟨hij, hjlen'⟩
