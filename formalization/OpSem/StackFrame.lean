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
  (.seq [
    .plain "A stack frame ",
    Doc.defMath (.raw "\\phi")
      (.text "StackFrame"),
    .plain " records the per-call state of a single function \
     activation: the MIR body being executed, the current \
     program counter, and the map from each local of that body \
     to the thin pointer identifying its stack allocation."])
where
  | body "The function body being executed." : Body
  | pc "The current program counter." : Location
  | locals "The per-local thin-pointer allocations."
      : Map Local ThinPointer
  deriving Repr

namespace StackFrame

defFn storageDeadPtr (.plain "storageDeadPtr")
  (.seq [.plain "Helper for ", .code "storageDead",
    .plain ": given a live thin pointer already looked up in ",
    .code "locals",
    .plain ", deallocate the backing allocation (when the \
    pointer has provenance) and remove the local's entry from ",
    .code "locals", .plain "."])
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage is being torn down." : Local)
  (ptr "The thin pointer currently bound to the local."
      : ThinPointer)
  : StackFrame × Memory where
  | frame ; mem ; l ; ⟨_, .some prov⟩ =>
      let newMem :=
        Memory.deallocate
          ‹mem, prov↦id, lean_proof("sorry")› ;
      let newLocals := mapRemove ‹frame↦locals, l› ;
      let newFrame :=
        StackFrame⟨frame↦body, frame↦pc, newLocals⟩ ;
      ⟨newFrame, newMem⟩
  | frame ; mem ; _ ; _ => ⟨frame, mem⟩

defFn storageDead (.plain "storageDead")
  (.seq [.plain "Tear down the stack allocation backing a \
    local, if one is live, returning the updated stack frame \
    (with the local removed from ", .code "locals",
    .plain ") together with the updated memory. If the local \
    has no entry in ", .code "locals",
    .plain ", the frame and memory are returned unchanged. \
    Mirrors MiniRust's ", .code "StackFrame::storage_dead",
    .plain " — alignment is ignored and the allocation kind \
    is implicitly ", .code "Stack", .plain "."])
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage should be torn down." : Local)
  : StackFrame × Memory :=
    match mapGet ‹frame↦locals, l› with
    | .none => ⟨frame, mem⟩
    | .some ptr => storageDeadPtr ‹frame, mem, l, ptr›
    end

defFn storageLive (.plain "storageLive")
  (.seq [.plain "Allocate stack storage for a local and bind \
    the resulting thin pointer into ", .code "locals",
    .plain ". First tears down any prior allocation for the \
    same local via ", .code "storageDead",
    .plain ", then looks up the local's type on the current \
    body's declarations, computes its size via ",
    Doc.refLinkOf @Ty.sizeOf "Ty.sizeOf", .plain ", and allocates that many \
    bytes. ", Doc.refLinkOf @validBody "validBody",
    .plain " guarantees every declared local type is sized, \
    so this is total."])
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage should be brought live." : Local)
  : StackFrame × Memory :=
    let ⟨frame1, mem1⟩ := storageDead ‹frame, mem, l› ;
    let ty := frame1↦body↦decls ! l↦index ;
    let sz := Ty.sizeOf ‹ty, lean_proof("sorry")› ;
    let addr := Memory.top ‹mem1› ;
    let ⟨mem2, aid⟩ := Memory.allocate ‹mem1, sz› ;
    let ptr :=
      ThinPointer⟨addr, Some Provenance⟨aid⟩⟩ ;
    let newLocals :=
      mapInsert ‹frame1↦locals, l, ptr› ;
    let newFrame :=
      StackFrame⟨frame1↦body, frame1↦pc, newLocals⟩ ;
    ⟨newFrame, mem2⟩

end StackFrame

defProperty validStackFrame (.plain "validStackFrame")
  short
    (.seq [frame, .plain " is a valid stack frame"])
  long
    (.seq [.plain "the body of ", frame,
           .plain " is a valid body, and the program \
           counter of ", frame,
           .plain " is a valid location in that body"])
  (frame "The stack frame." : StackFrame)
  :=
    validBody ‹frame↦body› ∧
    validLocation ‹frame↦body, frame↦pc›

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
      mapValues ‹frame↦locals›·flatMap fun ptr =>
        ptrAllocations ‹ptr, mem›

defProperty validStack (.plain "validStack")
  short
    (.seq [stack, .plain " is a valid stack against ", mem])
  long
    (.seq [.plain "every frame in ", stack,
           .plain " is a valid stack frame, and the \
           allocations backing the locals across all frames \
           in ", stack,
           .plain " are pairwise non-overlapping in ", mem])
  (stack "The call stack." : List StackFrame)
  (mem "The memory." : Memory)
  :=
    let allocs := localAllocations ‹stack, mem› ;
    (stack·forAll fun frame => validStackFrame ‹frame›) ∧
    (∀∀ i, j .
      i < j < allocs·length →
      Allocation.nonOverlapping ‹allocs ! i, allocs ! j›)
