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

defRaw before => {
  def last := @List.getLast?
  def replicate := @List.replicate
  def listSet := @List.set
  def listTake := @List.take
  def listDrop := @List.drop
  open AbstractByte
}

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

/-! ## Frame-preservation lemmas for `Memory.allocate` and `Memory.deallocate`

`Memory.allocate` appends a single allocation to `allocs` at the next
free address (`top mem`); `Memory.deallocate` flips one allocation's
`live` field and leaves every address and the list length alone. The
preservation lemmas below let consumers (`StackFrame.storageLive`,
`StackFrame.storageDead`) lift `validMemory` and `validPtr` through
either operation. -/

defRaw after =>
/-- `Memory.allocate` increases `allocs.length` by exactly one.
    `Memory.allocate` appends a single fresh allocation onto the
    `allocs` list. -/
theorem Memory.allocate_allocs_length
    (m : Memory) (size : Nat) :
    (Memory.allocate m size).fst.allocs.length = m.allocs.length + 1 := by
  unfold Memory.allocate; simp

defRaw after =>
/-- `Memory.allocate` returns the next allocation id, equal to
    the count of allocations already in the input memory. -/
theorem Memory.allocate_aid_index
    (m : Memory) (size : Nat) :
    (Memory.allocate m size).snd.index = m.allocs.length := by
  unfold Memory.allocate; rfl

defRaw after =>
/-- `Memory.allocate` preserves the list-prefix of allocations:
    every existing allocation index `i` retains its identity. -/
theorem Memory.allocate_alloc_unchanged
    (m : Memory) (size : Nat) (i : Nat) (h : i < m.allocs.length) :
    (Memory.allocate m size).fst.allocs[i]! = m.allocs[i]! := by
  have h_app_len :
      i < (Memory.allocate m size).fst.allocs.length := by
    rw [Memory.allocate_allocs_length]; omega
  rw [getElem!_pos _ i h_app_len, getElem!_pos m.allocs i h]
  unfold Memory.allocate
  exact List.getElem_append_left h

defRaw after =>
/-- `Memory.allocate` preserves the `address` field of every
    existing allocation: the appended new allocation does not
    disturb earlier indices. -/
theorem Memory.allocate_alloc_address_unchanged
    (m : Memory) (size : Nat) (i : Nat) (h : i < m.allocs.length) :
    ((Memory.allocate m size).fst.allocs[i]!).address
      = (m.allocs[i]!).address := by
  rw [Memory.allocate_alloc_unchanged m size i h]

defRaw after =>
/-- `Memory.allocate` preserves `endAddr` for every existing
    allocation. -/
theorem Memory.allocate_alloc_endAddr_unchanged
    (m : Memory) (size : Nat) (i : Nat) (h : i < m.allocs.length) :
    Allocation.endAddr ((Memory.allocate m size).fst.allocs[i]!)
      = Allocation.endAddr (m.allocs[i]!) := by
  rw [Memory.allocate_alloc_unchanged m size i h]

defRaw after =>
/-- The new allocation produced by `Memory.allocate` sits at index
    `m.allocs.length` and has address `Memory.top m`. -/
theorem Memory.allocate_new_alloc_address
    (m : Memory) (size : Nat) :
    ((Memory.allocate m size).fst.allocs[m.allocs.length]!).address
      = Memory.top m := by
  have h_app_len :
      m.allocs.length < (Memory.allocate m size).fst.allocs.length := by
    rw [Memory.allocate_allocs_length]; omega
  rw [getElem!_pos _ m.allocs.length h_app_len]
  -- After `getElem!_pos`, the LHS is the unfolded `getElem` on the
  -- appended list; `unfold Memory.allocate` exposes the literal
  -- shape `m.allocs ++ [⟨..., top m, ...⟩]`. The index hits the
  -- single appended element, so `List.getElem_append_right` reduces
  -- to that element's `address` field, which is `Memory.top m`.
  unfold Memory.allocate
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

defRaw after =>
/-- For a `validMemory` `m`, the next free address `top m` is
    strictly above every existing allocation's `endAddr`. This is
    the key fact making `Memory.allocate` preserve `validMemory`:
    the freshly appended allocation lives strictly above all
    existing ones, so the strict-ordering invariant carries
    through to the new pair. -/
theorem Memory.endAddr_lt_top
    (m : Memory) (hvm : Memory.validMemory m) (i : Nat)
    (h : i < m.allocs.length) :
    Allocation.endAddr (m.allocs[i]!) < Memory.top m := by
  -- The list is non-empty, so `last m.allocs = some last_alloc`
  -- where `last_alloc = m.allocs[length - 1]!`. `top m =
  -- (endAddr last_alloc).addr + 1`, and we want
  -- `endAddr (allocs[i]!) < endAddr last_alloc + 1`. For
  -- `i = length - 1` it's reflexive `≤` plus strict `< +1`; for
  -- `i < length - 1` we chain through validMemory: `endAddr
  -- (allocs[i]) < (allocs[length-1]).address ≤ endAddr
  -- (allocs[length-1])`.
  have h_nonempty : m.allocs ≠ [] := fun heq => by
    rw [heq] at h; exact absurd h (Nat.not_lt_zero _)
  have h_last_idx : m.allocs.length - 1 < m.allocs.length :=
    Nat.sub_lt (List.length_pos_iff.mpr h_nonempty) Nat.one_pos
  have h_last_eq : last m.allocs = some (m.allocs[m.allocs.length - 1]!) := by
    unfold last
    rw [getElem!_pos m.allocs (m.allocs.length - 1) h_last_idx]
    rw [List.getLast?_eq_getElem?]
    rw [List.getElem?_eq_getElem h_last_idx]
  unfold Memory.top
  rw [h_last_eq]
  show (Allocation.endAddr (m.allocs[i]!)).addr
       < (Allocation.endAddr (m.allocs[m.allocs.length - 1]!)).addr + 1
  by_cases h_eq : i = m.allocs.length - 1
  · subst h_eq; omega
  · -- `i < length - 1`. Use validMemory: endAddr (allocs[i]) <
    -- (allocs[length-1]).address ≤ endAddr (allocs[length-1]).
    have hi_lt : i < m.allocs.length - 1 := by omega
    have h_pair := hvm i (m.allocs.length - 1) ⟨hi_lt, h_last_idx⟩
    have h_addr_le :
        (m.allocs[m.allocs.length - 1]!).address.addr
          ≤ (Allocation.endAddr (m.allocs[m.allocs.length - 1]!)).addr := by
      unfold Allocation.endAddr; simp
    have h_lhs_lt : (Allocation.endAddr (m.allocs[i]!)).addr
        < (m.allocs[m.allocs.length - 1]!).address.addr := h_pair
    omega

defRaw after =>
/-- `Memory.allocate` preserves `Memory.validMemory`. Existing
    pairs of allocations keep their addresses (and hence their
    strict ordering); the new allocation appended at the end has
    address `top m`, which by `endAddr_lt_top` is strictly above
    every existing `endAddr`. -/
theorem Memory.allocate_preserves_validMemory
    (m : Memory) (size : Nat) :
    Memory.validMemory m
    → Memory.validMemory (Memory.allocate m size).fst := by
  intro hvm
  unfold Memory.validMemory at *
  intro i j hpair
  obtain ⟨hij, hjlen⟩ := hpair
  rw [Memory.allocate_allocs_length] at hjlen
  -- `j < m.allocs.length + 1`. Either `j < m.allocs.length`
  -- (existing-existing pair, use original `hvm`) or
  -- `j = m.allocs.length` (existing-new pair, use
  -- `endAddr_lt_top`).
  by_cases hj_old : j < m.allocs.length
  · have hi_old : i < m.allocs.length := by omega
    rw [Memory.allocate_alloc_endAddr_unchanged m size i hi_old,
        Memory.allocate_alloc_address_unchanged m size j hj_old]
    exact hvm i j ⟨hij, hj_old⟩
  · have hj_eq : j = m.allocs.length := by omega
    have hi_old : i < m.allocs.length := by omega
    rw [hj_eq, Memory.allocate_alloc_endAddr_unchanged m size i hi_old,
        Memory.allocate_new_alloc_address]
    exact Memory.endAddr_lt_top m hvm i hi_old

defRaw after =>
/-- `Memory.allocate` preserves `validPtr`: pointer validity only
    depends on the allocation count of the memory, which only
    grows. -/
theorem Memory.allocate_preserves_validPtr
    {m : Memory} {ptr : ThinPointer} (size : Nat)
    (h : Memory.validPtr m ptr) :
    Memory.validPtr (Memory.allocate m size).fst ptr := by
  unfold Memory.validPtr at *
  obtain ⟨addr, provOpt⟩ := ptr
  cases provOpt with
  | none => simp at *
  | some prov =>
    simp only at h ⊢
    unfold Memory.validProvenance Memory.validAllocId at *
    rw [Memory.allocate_allocs_length]
    omega

defRaw after =>
/-- The freshly minted allocation id from `Memory.allocate` is a
    valid id in the post-allocate memory: its index equals the
    pre-allocate length, and the post-allocate length is
    pre-length + 1. -/
theorem Memory.validAllocId_allocate_snd
    (m : Memory) (size : Nat) :
    Memory.validAllocId (Memory.allocate m size).fst
      (Memory.allocate m size).snd := by
  unfold Memory.validAllocId
  rw [Memory.allocate_aid_index, Memory.allocate_allocs_length]
  omega

defRaw after =>
/-- `Memory.deallocate` preserves `allocs.length`: it replaces one
    allocation in-place via `listSet`. -/
theorem Memory.deallocate_allocs_length_unchanged
    (m : Memory) (id : AllocId) (h : Memory.validAllocId m id) :
    (Memory.deallocate m id h).allocs.length = m.allocs.length := by
  unfold Memory.deallocate
  unfold listSet; simp

defRaw after =>
/-- `Memory.deallocate` preserves the `address` field of every
    allocation. The "dead" allocation produced inside copies the
    original's address; `List.set` leaves every other index
    alone. -/
theorem Memory.deallocate_alloc_address_unchanged
    (m : Memory) (id : AllocId) (h : Memory.validAllocId m id)
    (i : Nat) (h_i : i < m.allocs.length) :
    ((Memory.deallocate m id h).allocs[i]!).address
      = (m.allocs[i]!).address := by
  have h_set_len : i < (Memory.deallocate m id h).allocs.length := by
    rw [Memory.deallocate_allocs_length_unchanged]; exact h_i
  rw [getElem!_pos _ i h_set_len, getElem!_pos m.allocs i h_i]
  unfold Memory.deallocate
  simp only [listSet]
  by_cases hi : i = id.index
  · subst hi
    rw [List.getElem_set_self]
    -- Bridge the `[id.index]!`-form used inside `deallocate`'s
    -- body construction with the `[id.index]'h`-form on the RHS:
    -- both are equal under proof of in-bounds.
    rw [getElem!_pos m.allocs id.index h]
    rfl
  · rw [List.getElem_set_ne (Ne.symm hi)]

defRaw after =>
/-- `Memory.deallocate` preserves `endAddr` for every allocation:
    same argument as `address`-preservation — the dead replacement
    allocation copies both `address` and `data` from the original. -/
theorem Memory.deallocate_alloc_endAddr_unchanged
    (m : Memory) (id : AllocId) (h : Memory.validAllocId m id)
    (i : Nat) (h_i : i < m.allocs.length) :
    Allocation.endAddr ((Memory.deallocate m id h).allocs[i]!)
      = Allocation.endAddr (m.allocs[i]!) := by
  have h_set_len : i < (Memory.deallocate m id h).allocs.length := by
    rw [Memory.deallocate_allocs_length_unchanged]; exact h_i
  rw [getElem!_pos _ i h_set_len, getElem!_pos m.allocs i h_i]
  unfold Memory.deallocate
  simp only [listSet]
  by_cases hi : i = id.index
  · subst hi
    rw [List.getElem_set_self]
    unfold Allocation.endAddr
    rw [getElem!_pos m.allocs id.index h]
    rfl
  · rw [List.getElem_set_ne (Ne.symm hi)]

defRaw after =>
/-- `Memory.deallocate` preserves `Memory.validMemory`: every
    allocation's `address` and `endAddr` are unchanged, so the
    strict-ordering invariant carries through pointwise. -/
theorem Memory.deallocate_preserves_validMemory
    (m : Memory) (id : AllocId) (h : Memory.validAllocId m id) :
    Memory.validMemory m
    → Memory.validMemory (Memory.deallocate m id h) := by
  intro hvm
  unfold Memory.validMemory at *
  intro i j hpair
  obtain ⟨hij, hjlen⟩ := hpair
  have hjlen' : j < m.allocs.length := by
    rw [Memory.deallocate_allocs_length_unchanged] at hjlen; exact hjlen
  have hilen' : i < m.allocs.length := by omega
  rw [Memory.deallocate_alloc_endAddr_unchanged m id h i hilen',
      Memory.deallocate_alloc_address_unchanged m id h j hjlen']
  exact hvm i j ⟨hij, hjlen'⟩

defRaw after =>
/-- `Memory.deallocate` preserves `validPtr`: only the
    allocation count enters `validPtr`, and it is unchanged. -/
theorem Memory.deallocate_preserves_validPtr
    {m : Memory} {ptr : ThinPointer}
    (id : AllocId) (h : Memory.validAllocId m id)
    (h_ptr : Memory.validPtr m ptr) :
    Memory.validPtr (Memory.deallocate m id h) ptr := by
  unfold Memory.validPtr at *
  obtain ⟨addr, provOpt⟩ := ptr
  cases provOpt with
  | none => simp at *
  | some prov =>
    simp only at h_ptr ⊢
    unfold Memory.validProvenance Memory.validAllocId at *
    rw [Memory.deallocate_allocs_length_unchanged]
    exact h_ptr
