import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body
import MIR.Place
import OpSem.Layout
import OpSem.Memory
import OpSem.Pointer

defStruct StackFrame (.raw "\\phi",
    .doc (.plain "StackFrame"))
  "Stack Frames"
  (.seq [
    .plain "A stack frame ",
    Doc.defMath (.raw "\\phi")
      (.doc (.plain "StackFrame")),
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
    .code "Ty.layout", .plain ", and allocates that many \
    bytes. Returns ", .code "None",
    .plain " when the local's layout cannot be determined \
    (type parameters, aliases, constructor types, or unsized \
    layouts)."])
  (frame "The stack frame." : StackFrame)
  (mem "The memory." : Memory)
  (l "The local whose storage should be brought live." : Local)
  : Option (StackFrame × Memory) :=
    let ⟨frame1, mem1⟩ := storageDead ‹frame, mem, l› ;
    let ty := frame1↦body↦decls ! l↦index ;
    match Ty.layout ‹ty› with
    | .some (.sized sz) =>
        let addr := Memory.top ‹mem1› ;
        match Memory.allocate ‹mem1, sz› with
        | ⟨mem2, aid⟩ =>
            let ptr :=
              ThinPointer⟨addr, Some Provenance⟨aid⟩⟩ ;
            let newLocals :=
              mapInsert ‹frame1↦locals, l, ptr› ;
            let newFrame :=
              StackFrame⟨frame1↦body, frame1↦pc,
                newLocals⟩ ;
            Some ⟨newFrame, mem2⟩
        end
    | _ => None
    end

end StackFrame

defProperty validStackFrame (.plain "validStackFrame")
  (frameDoc) =>
    (.seq [frameDoc, .plain " is a valid stack frame: its \
           program counter points at some statement of some \
           basic block, with both indices in range"])
  (frame "The stack frame." : StackFrame)
  :=
    frame↦pc↦block↦index < frame↦body↦blocks·length ∧
    frame↦pc↦stmtIdx <
      (frame↦body↦blocks ! frame↦pc↦block↦index)↦statements·length
