import Core.Dsl.DefFn
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw
import Core.Dsl.DefStruct
import MIR.Body
import MIR.Place
import OpSem.Layout
import OpSem.Memory
import OpSem.Pointer

defStruct StackFrame (.sym .phi,
    .text "StackFrame")
  "Stack Frames"
  (doc! "A stack frame \
    $ϕ ∈ _StackFrame_$ \
    records the per-call state of a single function \
    activation: the MIR body being executed, the current \
    program counter, and the map from each local of that body \
    to the thin pointer identifying its stack allocation.")
where
  | body "The function body being executed." : Body
  | pc "The current program counter." : Location
  | locals "The per-local thin-pointer allocations."
      : Map Local ThinPointer
  deriving Repr

namespace StackFrame

open Memory in
defProperty validStackFrame (.plain "validStackFrame")
  short
    (doc! "{frame} is a valid stack frame in {m}")
  long
    (doc! "the body of {frame} is a valid body, the program \
      counter of {frame} is a valid location in that body, \
      and every locals-map entry of {frame} carries a thin \
      pointer that is valid in {m}")
  (m "The memory." : Memory)
  (frame "The stack frame." : StackFrame)
  :=
    validBody frame↦body ∧
    validLocation frame↦body frame↦pc ∧
    (mapValues frame↦locals·forAll fun ptr => validPtr m ptr)

defProperty localsAllocated (.plain "localsAllocated")
  short
    (doc! "every local of {frame} with index in the half-open \
      range [{lo}, {hi}) is allocated")
  long
    (doc! "for every index $i$ with {lo} ≤ $i$ and $i$ < {hi}, \
      the local at index $i$ has an entry in {frame}'s locals \
      map (i.e. `mapGet frame.locals Local⟨i⟩` is `some _`, \
      not `none`)")
  (frame "The stack frame." : StackFrame)
  (lo "The lower bound on local indices (inclusive)." : Nat)
  (hi "The upper bound on local indices (exclusive)." : Nat)
  := ∀∀ i . lo ≤ i → i < hi →
      mapGet frame↦locals Local⟨i⟩ ≠ None

open Memory in
defFn storageDeadPtr (.plain "storageDeadPtr")
  (doc! "Helper for `storageDead`: given a live thin pointer already looked up in `locals`, \
    deallocate the backing allocation (when the pointer has provenance) and remove the local's entry \
    from `locals`. The #Memory.validPtr precondition discharges the #Memory.validAllocId \
    obligation of #[Memory.deallocate]: the `.some prov` arm has `validPtr mem ⟨_, .some prov⟩` \
    reducing through `validProvenance mem prov` to `validAllocId mem prov.id`.")
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage is being torn down." : Local)
  (ptr "The thin pointer currently bound to the local."
      : ThinPointer)
  requires validPtr mem ptr
  : StackFrame × Memory where
  | frame ; mem ; l ; ⟨_, .some prov⟩ =>
      let newMem :=
        Memory.deallocate
          mem prov↦id proof[h_validPtr] ;
      let newLocals := mapRemove frame↦locals l ;
      let newFrame :=
        StackFrame⟨frame↦body, frame↦pc, newLocals⟩ ;
      ⟨newFrame, newMem⟩
  | frame ; mem ; _ ; _ => ⟨frame, mem⟩

open Memory in
defFn storageDead (.plain "storageDead")
  (doc! "Tear down the stack allocation backing a local, if one is live, returning the updated \
    stack frame (with the local removed from `locals`) together with the updated memory. If the \
    local has no entry in `locals`, the frame and memory are returned unchanged. Mirrors MiniRust's \
    `StackFrame::storage_dead` — alignment is ignored and the allocation kind is implicitly `Stack`. \
    The #validLocal precondition mirrors the one carried by `storageLive`, keeping the two \
    storage-management operations on a consistent contract about the local's index range.")
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage should be torn down." : Local)
  requires validStackFrame mem frame, validLocal frame↦body l
  : StackFrame × Memory :=
    match heq : mapGet frame↦locals l with
    | .none => ⟨frame, mem⟩
    | .some ptr =>
        -- The locals map's third validity conjunct
        -- (`∀ ptr ∈ mapValues frame.locals, validPtr mem ptr`)
        -- discharges `storageDeadPtr`'s `validPtr` requirement
        -- once we know `ptr` is a value of the map. The
        -- `match heq : ... with` form propagates the equation
        -- `mapGet frame.locals l = some ptr` into the arm so
        -- `mem_mapValues_of_mapGet_eq_some` applies.
        storageDeadPtr frame mem l ptr
          proof[(by
            have hall : ∀ p ∈ mapValues frame.locals,
                validPtr mem p :=
              h_validStackFrame.2.2
            exact hall ptr
              (mem_mapValues_of_mapGet_eq_some heq))]
    end

defFn storageLive (.plain "storageLive")
  (doc! "Allocate stack storage for a local and bind the resulting thin pointer into `locals`. \
    First tears down any prior allocation for the same local via `storageDead`, then looks up the \
    local's type on the current body's declarations, computes its size via #Ty.sizeOf, and allocates \
    that many bytes. The #validStackFrame precondition gives us #validBody on `frame.body` — every \
    declared local type is sized — and the #validLocal precondition pins {l}'s index inside \
    `frame.body.decls`, so the size lookup is total. The local's type is looked up on the *original* \
    `frame.body` (rather than `frame1.body`) so the precondition's #validBody directly discharges \
    the #Ty.sizeOf obligation; `storageDead` doesn't change the body, so this is \
    semantics-preserving.")
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage should be brought live." : Local)
  requires validStackFrame mem frame, validLocal frame↦body l
  : StackFrame × Memory :=
    let ⟨frame1, mem1⟩ := storageDead frame mem l
      proof[h_validStackFrame] proof[h_pre1] ;
    let ty := frame↦body↦decls ! l↦index ;
    let sz := Ty.sizeOf ty
      proof[(by
        -- `h_validStackFrame.1.2.2.2.1 : ∀ t ∈ frame.body.decls, IsSized t`
        -- (`validBody = decls ≠ [] ∧ blocks ≠ [] ∧ … ∧
        -- decls.forAll IsSized ∧ numArgs < decls.length`, so
        -- `.1.2.2.2.1` reaches the `IsSized` clause through the
        -- `validBody` outer conjunct of the mem-threaded
        -- `validStackFrame`), and `h_pre1 : validLocal frame.body l`
        -- (the second precondition, named positionally because its
        -- argument list isn't a bare-var sequence the DSL can name
        -- as `h_validLocal`) pins the index in range, so
        -- `decls[l.index]!` reduces to `decls[l.index]` — in
        -- the list, discharging `IsSized` directly.
        show Ty.IsSized (frame.body.decls[l.index]!)
        rw [getElem!_pos frame.body.decls l.index h_pre1]
        exact h_validStackFrame.1.2.2.2.1 _
          (List.getElem_mem h_pre1))] ;
    let addr := Memory.top mem1 ;
    let ⟨mem2, aid⟩ := Memory.allocate mem1 sz ;
    let ptr :=
      ThinPointer⟨addr, Some Provenance⟨aid⟩⟩ ;
    let newLocals :=
      mapInsert frame1↦locals l ptr ;
    let newFrame :=
      StackFrame⟨frame1↦body, frame1↦pc, newLocals⟩ ;
    ⟨newFrame, mem2⟩

end StackFrame

defFn ptrAllocations (.plain "ptrAllocations")
  (.plain "The singleton list containing the allocation \
    backing a pointer, or the empty list when the pointer has \
    no provenance and so cannot be resolved to an allocation.")
  (ptr "The pointer." : ThinPointer)
  (mem "The memory." : Memory)
  : List Allocation where
  | ⟨_, .some prov⟩ ; mem => [mem↦allocs ! prov↦id↦index]
  | _ ; _ => []

defFn localAllocations (.plain "localAllocations")
  (.plain "All allocations backing the locals across every \
    frame in a call stack. Pointers without provenance are \
    skipped — they cannot be resolved to an allocation.")
  (stack "The call stack." : List StackFrame)
  (mem "The memory." : Memory)
  : List Allocation :=
    stack·flatMap fun frame =>
      mapValues frame↦locals·flatMap fun ptr =>
        ptrAllocations ptr mem

defProperty headDisjointTail (.plain "headDisjointTail")
  short
    (doc! "the local allocations of frame {h} are disjoint \
      from those of stack {t} in {mem}")
  long
    (doc! "every allocation backing a local of {h} occupies an \
      address range disjoint from every allocation backing a \
      local of any frame in {t}, in {mem}")
  (h "The head stack frame." : StackFrame)
  (t "The tail call stack." : List StackFrame)
  (mem "The memory." : Memory)
  :=
    (localAllocations [h] mem)·forAll fun a =>
      (localAllocations t mem)·forAll fun b =>
        Allocation.nonOverlapping a b

open StackFrame in
defInductiveProperty validStack
  "Valid Stack"
  (doc! "Validity of a call stack against a memory, defined \
    inductively over the stack: the empty stack is trivially \
    valid; a non-empty stack `h :: t` is valid when `h` is a \
    valid stack frame in the memory, the tail `t` is itself a \
    valid stack in the memory, and the allocations backing \
    `h`'s locals occupy address ranges disjoint from every \
    allocation backing the locals of any frame in `t` (i.e. \
    `headDisjointTail h t mem` holds).")
  (stack "The call stack." : List StackFrame)
  (mem "The memory." : Memory)
where
  | nil {mem : Memory}
      ⊢ validStack [] mem
  | cons {h : StackFrame} {t : List StackFrame} {mem : Memory}
      from (validStackFrame mem h,
            validStack t mem,
            headDisjointTail h t mem)
      ⊢ validStack (h :: t) mem

/-! ## Body / pc preservation lemmas

`storageDead` and `storageLive` only mutate the `locals` map: the
underlying body and the program counter are unchanged. Tagging the
following equations as `@[simp]` lets the auto-discharge tactic at
recursive callers (`simp_all [validStackFrame]`) re-prove
`validStackFrame` after the frame has been threaded through one of
these helpers without needing a manual proof argument. The lemmas
sit in `defRaw after` blocks so they appear in the generated Lean
project alongside the source build (downstream proofs in
`createFrame` use them to discharge the `validBody.numArgs <
decls.length` bound on `liveAndStoreArgs`'s precondition). -/

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageDeadPtr_body
    (frame : StackFrame) (mem : Memory) (l : Local) (ptr : ThinPointer)
    (h : Memory.validPtr mem ptr) :
    (StackFrame.storageDeadPtr frame mem l ptr h).fst.body = frame.body := by
  unfold StackFrame.storageDeadPtr; split <;> rfl

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageDeadPtr_pc
    (frame : StackFrame) (mem : Memory) (l : Local) (ptr : ThinPointer)
    (h : Memory.validPtr mem ptr) :
    (StackFrame.storageDeadPtr frame mem l ptr h).fst.pc = frame.pc := by
  unfold StackFrame.storageDeadPtr; split <;> rfl

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageDead_body
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (StackFrame.storageDead frame mem l h₁ h₂).fst.body = frame.body := by
  unfold StackFrame.storageDead; split <;> simp [StackFrame.storageDeadPtr_body]

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageDead_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (StackFrame.storageDead frame mem l h₁ h₂).fst.pc = frame.pc := by
  unfold StackFrame.storageDead; split <;> simp [StackFrame.storageDeadPtr_pc]

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageLive_body
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (StackFrame.storageLive frame mem l h₁ h₂).fst.body = frame.body := by
  unfold StackFrame.storageLive; simp

defRaw after =>
open StackFrame Memory in
@[simp] theorem StackFrame.storageLive_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (StackFrame.storageLive frame mem l h₁ h₂).fst.pc = frame.pc := by
  unfold StackFrame.storageLive; simp

-- The four `defRaw after` theorems below splice into both
-- the in-tree elaboration and the generated Lean project.
-- Each uses `open StackFrame Memory in theorem ...` so the
-- unqualified `validStackFrame` resolves in either namespace:
-- the in-tree source places it at `StackFrame.validStackFrame`
-- (it's defined inside this file's
-- `namespace StackFrame ... end StackFrame` block), while the
-- Lean exporter lifts it into `Memory.validStackFrame` (its
-- first param's type is `Memory`). The same dual-`open`
-- pattern handles `headDisjointTail`, which is top-level
-- in-tree but `StackFrame.headDisjointTail` in the generated
-- project (its first param is `StackFrame`).
defRaw after => {
open StackFrame Memory in
/-- The head of a non-empty `validStack` is itself a
    `validStackFrame` against the same memory. Direct
    projection of the cons rule's `validStackFrame mem h`
    premise. -/
theorem validStack.head
    {h : StackFrame} {t : List StackFrame} {mem : Memory}
    (hv : validStack (h :: t) mem) :
    validStackFrame mem h := by
  cases hv
  assumption

/-- The tail of a `validStack` is itself a `validStack`
    against the same memory. Direct projection of the cons
    rule's `validStack t mem` premise. -/
theorem validStack.tail
    {h : StackFrame} {t : List StackFrame} {mem : Memory}
    (hv : validStack (h :: t) mem) : validStack t mem := by
  cases hv
  assumption

open StackFrame in
/-- The non-overlap premise of `validStack`'s cons rule:
    `headDisjointTail h t mem` — every allocation in
    `localAllocations [h] mem` is disjoint from every
    allocation in `localAllocations t mem`. -/
theorem validStack.head_disjoint_tail
    {h : StackFrame} {t : List StackFrame} {mem : Memory}
    (hv : validStack (h :: t) mem) :
    headDisjointTail h t mem := by
  cases hv
  assumption

open StackFrame Memory in
/-- Every frame appearing in a `validStack` is itself a
    `validStackFrame` against the same memory. Recurses on the
    list, peeling off the head with `validStack.head` and
    delegating to the tail (a `validStack` by
    `validStack.tail`) for the rest. -/
theorem validStack.frame_valid
    {stack : List StackFrame} {mem : Memory}
    (h : validStack stack mem)
    {f : StackFrame} (hf : f ∈ stack) :
    validStackFrame mem f := by
  induction stack with
  | nil => exact absurd hf List.not_mem_nil
  | cons hd tl ih =>
    rcases List.mem_cons.mp hf with rfl | h_in_t
    · exact validStack.head h
    · exact ih (validStack.tail h) h_in_t
}

defRaw after => {
open Memory in
/-- `Memory.store` preserves `validPtr`: pointer validity only
    depends on the allocation count of the memory, which
    `Memory.store` preserves. -/
theorem Memory.validPtr_store_preserves
    {m : Memory} {ptr : ThinPointer}
    (storePtr : ThinPointer) (storeBytes : List AbstractByte)
    (h : validPtr m ptr) :
    validPtr (Memory.store m storePtr storeBytes) ptr := by
  unfold validPtr at *
  obtain ⟨addr, provOpt⟩ := ptr
  cases provOpt with
  | none => simp at *
  | some prov =>
    simp only at h
    simp only
    unfold validProvenance validAllocId at *
    rw [Memory.store_allocs_length_unchanged]
    exact h

open StackFrame Memory in
/-- `Memory.store` preserves `validStackFrame`: the body and
    program counter clauses are independent of memory; the
    pointer-validity clause is preserved by
    `validPtr_store_preserves`. -/
theorem StackFrame.validStackFrame_store_preserves
    {m : Memory} {frame : StackFrame}
    (ptr : ThinPointer) (bytes : List AbstractByte)
    (h : validStackFrame m frame) :
    validStackFrame (Memory.store m ptr bytes) frame := by
  unfold validStackFrame at *
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp
  exact Memory.validPtr_store_preserves _ _ (h.2.2 p hp)

/-- `Memory.store` preserves `ptrAllocations`: the lookup uses
    only the `address` and `data.length` of the targeted
    allocation, both of which `Memory.store` leaves alone (its
    `endAddr` is also preserved). The full equality follows
    once we show the looked-up allocation matches structurally;
    instead of equality on the lists, we record the pointwise
    `endAddr`/`address` preservation needed by
    `nonOverlapping`. -/
theorem ptrAllocations_endAddr_address_preserved
    {mem : Memory} (p : ThinPointer)
    (storePtr : ThinPointer) (storeBytes : List AbstractByte) :
    ∀ a ∈ ptrAllocations p (Memory.store mem storePtr storeBytes),
      ∃ a' ∈ ptrAllocations p mem,
        a.address = a'.address ∧ Allocation.endAddr a = Allocation.endAddr a' := by
  intro a ha
  unfold ptrAllocations at *
  -- `ptrAllocations` matches on the pointer's provenance;
  -- destructure `p` so the match arms reduce.
  obtain ⟨addr, provOpt⟩ := p
  cases provOpt with
  | none => simp at ha
  | some prov =>
    simp at ha
    -- `a` is the looked-up allocation in the stored memory at
    -- index `prov.id.index`. Either that index is in range or
    -- not.
    -- Bridge `[..]?.getD default` with `[..]!` so the
    -- store-preservation lemmas line up.
    have h_bridge_lhs :
        (Memory.store mem storePtr storeBytes).allocs[prov.id.index]?.getD default
          = (Memory.store mem storePtr storeBytes).allocs[prov.id.index]! := by
      cases h : (Memory.store mem storePtr storeBytes).allocs[prov.id.index]? <;> simp [h]
    rw [h_bridge_lhs] at ha
    by_cases h_idx : prov.id.index < mem.allocs.length
    · refine ⟨mem.allocs[prov.id.index]!, by simp, ?_, ?_⟩
      · rw [ha]
        exact Memory.store_alloc_address_unchanged mem storePtr storeBytes
          prov.id.index h_idx
      · rw [ha]
        exact Memory.store_alloc_endAddr_unchanged mem storePtr storeBytes
          prov.id.index h_idx
    · -- Out-of-range: `getElem!` returns `default`; the store
      -- preserves list length, so both sides are `default`.
      have h_eq_len :
          (Memory.store mem storePtr storeBytes).allocs.length = mem.allocs.length :=
        Memory.store_allocs_length_unchanged mem storePtr storeBytes
      have h_idx' :
          ¬ prov.id.index < (Memory.store mem storePtr storeBytes).allocs.length := by
        rw [h_eq_len]; exact h_idx
      have h_def_lhs :
          (Memory.store mem storePtr storeBytes).allocs[prov.id.index]! =
            (default : Allocation) :=
        getElem!_neg _ prov.id.index h_idx'
      refine ⟨mem.allocs[prov.id.index]!, by simp, ?_, ?_⟩
      · rw [ha, h_def_lhs]
        exact (getElem!_neg mem.allocs prov.id.index h_idx).symm ▸ rfl
      · rw [ha, h_def_lhs]
        exact (getElem!_neg mem.allocs prov.id.index h_idx).symm ▸ rfl

/-- `Memory.store` preserves `headDisjointTail`. This rests on
    `nonOverlapping` only depending on each allocation's
    `address` and `endAddr`, both of which `Memory.store`
    preserves. -/
theorem headDisjointTail_store_preserves
    {h : StackFrame} {t : List StackFrame} {mem : Memory}
    (ptr : ThinPointer) (bytes : List AbstractByte)
    (hd : headDisjointTail h t mem) :
    headDisjointTail h t (Memory.store mem ptr bytes) := by
  unfold headDisjointTail localAllocations at *
  -- `·forAll` lowers to `∀ x ∈ list, body`. Introduce `a` from
  -- the head's allocations and `b` from the tail's, both
  -- indexed in the *stored* memory; then track each one back
  -- to a local allocation in the original `mem` via
  -- `ptrAllocations_endAddr_address_preserved`. The head's
  -- `[h].flatMap` collapses to a single `mem_flatMap` step;
  -- the tail's `t.flatMap` is one `mem_flatMap` over the
  -- frame, then another over the locals' pointers.
  intro a ha b hb
  -- Head: `a ∈ [h].flatMap (...)` collapses (one frame in the
  -- list) to `a ∈ (mapValues h.locals).flatMap …`. Tail: `b ∈
  -- t.flatMap …` is one `mem_flatMap` over the frame, then
  -- another over the locals' pointers.
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_flatMap] at ha
  rw [List.mem_flatMap] at hb
  obtain ⟨pa, hpa, ha_in⟩ := ha
  obtain ⟨frame_b, hframe_b, hb⟩ := hb
  rw [List.mem_flatMap] at hb
  obtain ⟨pb, hpb, hb_in⟩ := hb
  obtain ⟨a', ha'_in, ha'_addr, ha'_end⟩ :=
    ptrAllocations_endAddr_address_preserved pa ptr bytes a ha_in
  obtain ⟨b', hb'_in, hb'_addr, hb'_end⟩ :=
    ptrAllocations_endAddr_address_preserved pb ptr bytes b hb_in
  have h_orig := hd a'
    (by rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_flatMap]
        exact ⟨pa, hpa, ha'_in⟩)
    b' (List.mem_flatMap.mpr ⟨frame_b, hframe_b,
      List.mem_flatMap.mpr ⟨pb, hpb, hb'_in⟩⟩)
  unfold Allocation.nonOverlapping at *
  rw [ha'_end, hb'_addr, hb'_end, ha'_addr]
  exact h_orig

/-- `Memory.store` preserves `validStack`. The three
    constituents of `validStack` (`validStackFrame`,
    `validStack` of the tail, `headDisjointTail`) are each
    preserved by the matching `Memory.store_preserves` lemma:
    `validStackFrame_store_preserves`, the inductive
    hypothesis on the tail, and
    `headDisjointTail_store_preserves`. -/
theorem validStack.store_preserves
    {stack : List StackFrame} {mem : Memory}
    (ptr : ThinPointer) (bytes : List AbstractByte)
    (h : validStack stack mem) :
    validStack stack (Memory.store mem ptr bytes) := by
  induction h with
  | nil => exact validStack.nil
  | cons h_vsf h_vs h_disj ih =>
    apply validStack.cons
    · exact StackFrame.validStackFrame_store_preserves _ _ h_vsf
    · exact ih
    · exact headDisjointTail_store_preserves _ _ h_disj
}

/-! ## Frame-preservation lemmas for `storageDead` and `storageLive`

`storageDead` either returns the input unchanged (when the local has no
entry in `locals`) or, via `storageDeadPtr`, deallocates one allocation
and removes the local's entry. `storageLive` always runs `storageDead`
first, then `Memory.allocate`s a fresh allocation and binds the local
to a pointer with that fresh provenance. The two preservation lemmas
below let `createFrame` discharge `validMemory` / `validStackFrame` on
the post-`storageLive` state. -/

defRaw after => {
open StackFrame Memory in
/-- `storageDeadPtr` preserves `validMemory`: the only memory mutation
    is `Memory.deallocate`, which preserves `validMemory`. The proof
    proceeds by `cases` on the pointer's provenance — only the
    `.some prov` arm runs `Memory.deallocate`, the `.none` arm leaves
    the memory unchanged. -/
theorem StackFrame.storageDeadPtr_preserves_validMemory
    {frame : StackFrame} {mem : Memory} {l : Local} (ptr : ThinPointer)
    (h : validPtr mem ptr) (hvm : validMemory mem) :
    validMemory (storageDeadPtr frame mem l ptr h).snd := by
  obtain ⟨addr, provOpt⟩ := ptr
  cases provOpt with
  | some prov =>
    unfold storageDeadPtr
    simp only
    exact Memory.deallocate_preserves_validMemory mem prov.id h hvm
  | none =>
    unfold storageDeadPtr
    simp only
    exact hvm

open StackFrame Memory in
/-- `storageDead` preserves `validMemory`. Either the local has no
    entry (the memory is returned unchanged) or `storageDeadPtr` is
    invoked, which preserves `validMemory` by
    `storageDeadPtr_preserves_validMemory`. -/
theorem StackFrame.storageDead_preserves_validMemory
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l)
    (hvm : validMemory mem) :
    validMemory (storageDead frame mem l h₁ h₂).snd := by
  unfold storageDead
  split
  · exact hvm
  · exact StackFrame.storageDeadPtr_preserves_validMemory _ _ hvm

open StackFrame Memory in
/-- `storageLive` preserves `validMemory`: combines
    `storageDead_preserves_validMemory` (the inner `storageDead` step)
    and `Memory.allocate_preserves_validMemory` (the subsequent
    `Memory.allocate` step). -/
theorem StackFrame.storageLive_preserves_validMemory
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l)
    (hvm : validMemory mem) :
    validMemory (storageLive frame mem l h₁ h₂).snd := by
  unfold storageLive
  simp only
  exact Memory.allocate_preserves_validMemory _ _
    (storageDead_preserves_validMemory frame mem l h₁ h₂ hvm)
}

defRaw after =>
open StackFrame Memory in
/-- `storageDeadPtr` preserves `validPtr`: `Memory.deallocate`
    preserves `validPtr` (count-based) and the unchanged-memory arm
    is trivial. -/
theorem StackFrame.storageDeadPtr_preserves_validPtr
    {frame : StackFrame} {mem : Memory} {l : Local} {ptr_d : ThinPointer}
    (h_d : validPtr mem ptr_d)
    {ptr : ThinPointer} (h_p : validPtr mem ptr) :
    validPtr (storageDeadPtr frame mem l ptr_d h_d).snd ptr := by
  obtain ⟨addr, provOpt⟩ := ptr_d
  cases provOpt with
  | some prov =>
    unfold storageDeadPtr
    simp only
    exact Memory.deallocate_preserves_validPtr prov.id h_d h_p
  | none =>
    unfold storageDeadPtr
    simp only
    exact h_p

defRaw after =>
open StackFrame Memory in
/-- `storageDead` preserves `validPtr`: either the memory is
    unchanged or `storageDeadPtr_preserves_validPtr` applies. -/
theorem StackFrame.storageDead_preserves_validPtr
    {frame : StackFrame} {mem : Memory} {l : Local}
    {h₁ : validStackFrame mem frame} {h₂ : validLocal frame.body l}
    {ptr : ThinPointer} (h_p : validPtr mem ptr) :
    validPtr (storageDead frame mem l h₁ h₂).snd ptr := by
  unfold storageDead
  split
  · exact h_p
  · exact StackFrame.storageDeadPtr_preserves_validPtr _ h_p

defRaw after =>
open StackFrame Memory in
/-- `storageDeadPtr` preserves `validStackFrame`: the dropped
    locals entry is the only locals-map change (via `mapRemove`),
    and `Memory.deallocate` preserves `validPtr` for every
    remaining pointer (count-based). -/
theorem StackFrame.storageDeadPtr_preserves_validStackFrame
    {frame : StackFrame} {mem : Memory} {l : Local} {ptr_d : ThinPointer}
    (h_d : validPtr mem ptr_d)
    (h₁ : validStackFrame mem frame) :
    validStackFrame (storageDeadPtr frame mem l ptr_d h_d).snd
                    (storageDeadPtr frame mem l ptr_d h_d).fst := by
  obtain ⟨addr, provOpt⟩ := ptr_d
  cases provOpt with
  | some prov =>
    unfold storageDeadPtr
    simp only
    refine ⟨h₁.1, h₁.2.1, ?_⟩
    -- New locals = mapRemove frame.locals l, only ever drops
    -- entries; lift each remaining ptr's validity through
    -- `Memory.deallocate_preserves_validPtr`.
    intro ptr hptr
    have hptr_orig : ptr ∈ mapValues frame.locals :=
      mem_mapValues_mapRemove hptr
    exact Memory.deallocate_preserves_validPtr prov.id h_d
      (h₁.2.2 ptr hptr_orig)
  | none =>
    unfold storageDeadPtr
    simp only
    exact h₁

defRaw after =>
open StackFrame Memory in
/-- `storageDead` preserves `validStackFrame`: either the
    memory and frame are returned unchanged (the `.none` arm)
    or `storageDeadPtr_preserves_validStackFrame` applies. -/
theorem StackFrame.storageDead_preserves_validStackFrame
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    validStackFrame (storageDead frame mem l h₁ h₂).snd
                    (storageDead frame mem l h₁ h₂).fst := by
  unfold storageDead
  split
  · exact h₁
  · exact StackFrame.storageDeadPtr_preserves_validStackFrame _ h₁

defRaw after =>
open StackFrame Memory in
/-- `Memory.allocate` preserves `validStackFrame`: body and pc are
    independent of memory; existing locals' validity (count-based)
    is preserved by `Memory.allocate_preserves_validPtr`. -/
theorem StackFrame.validStackFrame_allocate_preserves
    {mem : Memory} {frame : StackFrame} (size : Nat)
    (h : validStackFrame mem frame) :
    validStackFrame (Memory.allocate mem size).fst frame := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro ptr hptr
  exact Memory.allocate_preserves_validPtr size (h.2.2 ptr hptr)

defRaw after =>
open StackFrame Memory in
/-- `storageLive` preserves `validStackFrame`: body and pc are
    unchanged by construction; the new locals map's only fresh
    entry is the freshly-allocated pointer (whose provenance has
    index `< new mem.allocs.length` by
    `validAllocId_allocate_snd`), and the remaining entries lift
    via `Memory.allocate_preserves_validPtr` over the inner
    post-`storageDead` frame.

    Body and pc preservation are re-proved inline via
    `unfold storageLive; simp` (the source's `@[simp] theorem
    storageLive_body` / `_pc` are not propagated to the generated
    project, so referencing them here would break the export). -/
theorem StackFrame.storageLive_preserves_validStackFrame
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    validStackFrame (storageLive frame mem l h₁ h₂).snd
                    (storageLive frame mem l h₁ h₂).fst := by
  have h_body : (storageLive frame mem l h₁ h₂).fst.body = frame.body := by
    unfold storageLive; simp [storageDead]; split <;> simp [storageDeadPtr]
    split <;> rfl
  have h_pc : (storageLive frame mem l h₁ h₂).fst.pc = frame.pc := by
    unfold storageLive; simp [storageDead]; split <;> simp [storageDeadPtr]
    split <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [h_body]; exact h₁.1
  · rw [h_body, h_pc]; exact h₁.2.1
  · -- Every ptr in the new locals: either it's the fresh pointer
    -- bound to `l` (validProvenance via `validAllocId_allocate_snd`)
    -- or it's an existing ptr from the post-`storageDead` frame's
    -- locals (validPtr lifts via `allocate_preserves_validPtr`).
    intro ptr hptr
    unfold storageLive at hptr
    simp only at hptr
    rcases mem_mapValues_mapInsert hptr with rfl | hptr_old
    · -- Fresh pointer: validPtr by validAllocId_allocate_snd.
      unfold validPtr
      simp only
      unfold validProvenance
      exact Memory.validAllocId_allocate_snd _ _
    · -- Existing pointer from the post-`storageDead` frame's
      -- locals: its validity in the post-`storageDead` memory is
      -- given by `storageDead_preserves_validStackFrame`'s third
      -- conjunct; `Memory.allocate_preserves_validPtr` then lifts
      -- to the post-`allocate` memory.
      have h_dd := storageDead_preserves_validStackFrame frame mem l h₁ h₂
      have h_old := h_dd.2.2 ptr hptr_old
      exact Memory.allocate_preserves_validPtr _ h_old

defRaw after =>
open StackFrame Memory in
/-- `storageLive frame mem ⟨k⟩ _ _` extends `localsAllocated`
    from the half-open range `[1, k)` to `[1, k+1)`: the
    freshly-bound pointer at `⟨k⟩` adds the missing index, and
    indices `i < k` retain their entries (the inner `storageDead`
    can only erase the entry at `⟨k⟩`, leaving `⟨i⟩` for `i ≠ k`
    untouched, and the outer `mapInsert` likewise preserves
    lookups at `⟨i⟩ ≠ ⟨k⟩`). Used to discharge `liveAndStoreArgs`'s
    recursive-call `localsAllocated frame1 1 (k+1)` precondition
    without going through `liveAndStoreArgs.precondAxiom`. -/
theorem StackFrame.storageLive_localsAllocated_extend
    {frame : StackFrame} {mem : Memory} {k : Nat}
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body ⟨k⟩)
    (h_alloc : localsAllocated frame 1 k) :
    localsAllocated (storageLive frame mem ⟨k⟩ h₁ h₂).fst 1 (k + 1) := by
  intro i hlo hhi
  -- The new frame's locals = mapInsert (storageDead-frame).locals ⟨k⟩ ptr_new.
  -- Lookup at ⟨i⟩ via `getElem?_insert`: branches on `⟨k⟩ == ⟨i⟩`.
  show mapGet (storageLive frame mem ⟨k⟩ h₁ h₂).fst.locals ⟨i⟩ ≠ .none
  unfold storageLive
  simp only
  unfold mapInsert mapGet
  rw [Std.HashMap.get?_insert]
  by_cases h_eq : k = i
  · subst h_eq; simp
  · -- `i ≠ k`. Since `i < k+1`, we have `i < k`.
    have h_lt : i < k := by omega
    have h_neq_beq : ((⟨k⟩ : Local) == ⟨i⟩) = false := by
      apply Bool.eq_false_iff.mpr
      intro hk
      simp [BEq.beq, instBEqLocal.beq] at hk
      exact h_eq hk
    rw [h_neq_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Goal: (storageDead-frame).locals.get? ⟨i⟩ ≠ none.
    -- For `i ≠ k`, the inner `storageDead` preserves the entry at
    -- `⟨i⟩` (whether it no-ops or erases the entry at `⟨k⟩`).
    have h_dd_lookup :
        (storageDead frame mem ⟨k⟩ h₁ h₂).fst.locals.get? ⟨i⟩
          = frame.locals.get? ⟨i⟩ := by
      unfold storageDead
      split
      · rfl
      · rename_i ptr_d _
        unfold storageDeadPtr
        split
        · simp only
          unfold mapRemove
          rw [Std.HashMap.get?_erase]
          rw [show ((⟨k⟩ : Local) == ⟨i⟩) = false from h_neq_beq]
          rfl
        · rfl
    rw [h_dd_lookup]
    exact h_alloc i hlo h_lt

