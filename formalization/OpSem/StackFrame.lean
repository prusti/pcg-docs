import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body
import MIR.Place
import OpSem.Layout
import OpSem.Memory
import OpSem.Pointer

defStruct StackFrame (.raw "\\phi",
    .text "StackFrame")
  "Stack Frames"
  (doc! "A stack frame \
    $\\phi ∈ _StackFrame_$ \
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

defProperty validStackFrame (.plain "validStackFrame")
  short
    (doc! "{frame} is a valid stack frame")
  long
    (doc! "the body of {frame} is a valid body, and the \
      program counter of {frame} is a valid location in that \
      body")
  (frame "The stack frame." : StackFrame)
  :=
    validBody frame↦body ∧
    validLocation frame↦body frame↦pc

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
  requires validLocal frame↦body l
  : StackFrame × Memory :=
    match mapGet frame↦locals l with
    | .none => ⟨frame, mem⟩
    | .some ptr =>
        -- The new `validPtr` obligation on `storageDeadPtr`
        -- propagates up to here; a per-frame validity
        -- invariant (every pointer in `frame.locals` is a
        -- valid pointer in `mem`) would discharge it, but
        -- threading that through is left for a follow-up.
        storageDeadPtr frame mem l ptr proof[sorry]
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
  requires validStackFrame frame, validLocal frame↦body l
  : StackFrame × Memory :=
    let ⟨frame1, mem1⟩ := storageDead frame mem l
      proof[h_pre1] ;
    let ty := frame↦body↦decls ! l↦index ;
    let sz := Ty.sizeOf ty
      proof[(by
        -- `h_validStackFrame.1.2.2 : ∀ t ∈ frame.body.decls, IsSized t`
        -- (`validBody` is `decls ≠ [] ∧ (∀ bb …) ∧ (∀ t …,
        -- IsSized t)`, so the `.2.2` projection picks out the
        -- third conjunct), and `h_pre1 : validLocal frame.body
        -- l` (the second precondition, named positionally
        -- because its argument list isn't a bare-var sequence
        -- the DSL can name as `h_validLocal`) pins the index
        -- in range, so `decls[l.index]!` reduces to
        -- `decls[l.index]` — in the list, discharging
        -- `IsSized` directly.
        show Ty.IsSized (frame.body.decls[l.index]!)
        rw [getElem!_pos frame.body.decls l.index h_pre1]
        exact h_validStackFrame.1.2.2 _
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
    (h : validLocal frame.body l) :
    (storageDead frame mem l h).fst.body = frame.body := by
  unfold storageDead; split <;> simp [storageDeadPtr_body]

@[simp] theorem storageDead_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h : validLocal frame.body l) :
    (storageDead frame mem l h).fst.pc = frame.pc := by
  unfold storageDead; split <;> simp [storageDeadPtr_pc]

@[simp] theorem storageLive_body
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame frame) (h₂ : validLocal frame.body l) :
    (storageLive frame mem l h₁ h₂).fst.body = frame.body := by
  unfold storageLive; simp

@[simp] theorem storageLive_pc
    (frame : StackFrame) (mem : Memory) (l : Local)
    (h₁ : validStackFrame frame) (h₂ : validLocal frame.body l) :
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

defProperty validStack (.plain "validStack")
  short
    (doc! "{stack} is a valid stack against {mem}")
  long
    (doc! "every frame in {stack} is a valid stack frame, and \
      the allocations backing the locals across all frames in \
      {stack} are pairwise non-overlapping in {mem}")
  (stack "The call stack." : List StackFrame)
  (mem "The memory." : Memory)
  :=
    let allocs := localAllocations stack mem ;
    (stack·forAll fun frame => StackFrame.validStackFrame frame) ∧
    (∀∀ i, j .
      i < j < allocs·length →
      Allocation.nonOverlapping (allocs ! i) (allocs ! j))
