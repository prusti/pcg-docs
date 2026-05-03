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
        -- `h_validStackFrame.1.2.2.2 : ∀ t ∈ frame.body.decls, IsSized t`
        -- (`validBody = decls ≠ [] ∧ blocks ≠ [] ∧ … ∧
        -- decls.forAll IsSized`, so `.1.2.2.2` reaches the
        -- `IsSized` clause through the `validBody` outer
        -- conjunct of the mem-threaded `validStackFrame`), and
        -- `h_pre1 : validLocal frame.body l` (the second
        -- precondition, named positionally because its argument
        -- list isn't a bare-var sequence the DSL can name as
        -- `h_validLocal`) pins the index in range, so
        -- `decls[l.index]!` reduces to `decls[l.index]` — in
        -- the list, discharging `IsSized` directly.
        show Ty.IsSized (frame.body.decls[l.index]!)
        rw [getElem!_pos frame.body.decls l.index h_pre1]
        exact h_validStackFrame.1.2.2.2 _
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

/-! ## Body / pc preservation lemmas

`storageDead` and `storageLive` only mutate the `locals` map: the
underlying body and the program counter are unchanged. Tagging the
following equations as `@[simp]` lets the auto-discharge tactic at
recursive callers (`simp_all [validStackFrame]`) re-prove
`validStackFrame` after the frame has been threaded through one of
these helpers without needing a manual proof argument. -/

@[simp] theorem storageDeadPtr_body
    (frame : StackFrame) (mem : Memory) (l : Local) (ptr : ThinPointer)
    (h : Memory.validPtr mem ptr) :
    (storageDeadPtr frame mem l ptr h).fst.body = frame.body := by
  unfold storageDeadPtr; split <;> rfl

@[simp] theorem storageDeadPtr_pc
    (frame : StackFrame) (mem : Memory) (l : Local) (ptr : ThinPointer)
    (h : Memory.validPtr mem ptr) :
    (storageDeadPtr frame mem l ptr h).fst.pc = frame.pc := by
  unfold storageDeadPtr; split <;> rfl

@[simp] theorem storageDead_body
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (storageDead frame mem l h₁ h₂).fst.body = frame.body := by
  unfold storageDead; split <;> simp [storageDeadPtr_body]

@[simp] theorem storageDead_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (storageDead frame mem l h₁ h₂).fst.pc = frame.pc := by
  unfold storageDead; split <;> simp [storageDeadPtr_pc]

@[simp] theorem storageLive_body
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (storageLive frame mem l h₁ h₂).fst.body = frame.body := by
  unfold storageLive; simp

@[simp] theorem storageLive_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame mem frame) (h₂ : validLocal frame.body l) :
    (storageLive frame mem l h₁ h₂).fst.pc = frame.pc := by
  unfold storageLive; simp

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
defRaw after =>
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

defRaw after =>
/-- The tail of a `validStack` is itself a `validStack`
    against the same memory. Direct projection of the cons
    rule's `validStack t mem` premise. -/
theorem validStack.tail
    {h : StackFrame} {t : List StackFrame} {mem : Memory}
    (hv : validStack (h :: t) mem) : validStack t mem := by
  cases hv
  assumption

defRaw after =>
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

defRaw after =>
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
