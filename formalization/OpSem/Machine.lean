import OpSem.Memory
import OpSem.Program
import OpSem.PlacePtr
import OpSem.Thread
import OpSem.Value
import OpSem.Decode
import MIR.Body
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct Machine (.raw "\\mu", .text "Machine")
  "Machines"
  (.seq [
    .plain "A machine state ",
    Doc.defMath (.raw "\\mu") (.text "Machine"),
    .plain " bundles the whole program being executed, the \
     single-threaded execution context, and the shared memory. \
     Per-call state — the function body, program counter, and \
     local pointer map — lives on the thread's current stack \
     frame."])
where
  | program "The program being executed." : Program
  | thread "The single thread of execution." : Thread
  | mem "The memory." : Memory
  deriving Repr

namespace Machine

defProperty Runnable (.plain "Runnable")
  short
    (.seq [m, .plain " is a runnable machine"])
  long
    (.seq [.plain "the call stack of ", m,
           .plain " is non-empty, the program of ", m,
           .plain " is valid, and the call stack of ", m,
           .plain " is a valid stack against the memory of ",
           m])
  (m "The machine state." : Machine)
  :=
    m↦thread↦stack ≠ [] ∧
    validProgram ‹m↦program› ∧
    validStack ‹m↦thread↦stack, m↦mem›

-- Source-only `Inhabited StackFrame` so `head!` inside
-- `currentFrame` (which relies on the precondition for
-- safety) elaborates against the source `defStruct`, which
-- only derives `Repr`. The Lean exporter adds `Inhabited`
-- automatically to the corresponding generated declaration,
-- so this is not re-emitted there.
private instance : Inhabited StackFrame :=
  ⟨⟨⟨[], 0, []⟩, ⟨⟨0⟩, 0⟩, ∅⟩⟩

defFn currentFrame (.plain "currentFrame")
  (.plain "The currently executing stack frame, i.e. the head \
    of the thread's call stack. Safe because the \
    `Runnable` precondition guarantees the stack is \
    non-empty.")
  (m "The machine state." : Machine)
  requires Runnable(m)
  : StackFrame :=
    m↦thread↦stack·head!

defFn currBody (.plain "currBody")
  (.seq [.plain "The body of the currently executing stack \
    frame. Shorthand for ", .code "currentFrame",
    .plain "'s ", .code "body", .plain " field; safe under \
    the same ", .code "Runnable", .plain " precondition."])
  (m "The machine state." : Machine)
  requires Runnable(m)
  : Body :=
    (currentFrame ‹m, lean_proof("h_Runnable")›)↦body

defFn currPC (.plain "currPC")
  (.seq [.plain "The program counter of the currently \
    executing stack frame. Shorthand for ",
    .code "currentFrame", .plain "'s ", .code "pc",
    .plain " field; safe under the same ",
    .code "Runnable", .plain " precondition."])
  (m "The machine state." : Machine)
  requires Runnable(m)
  : Location :=
    (currentFrame ‹m, lean_proof("h_Runnable")›)↦pc

defFn stackTail (.plain "stackTail")
  (.seq [.plain "The tail of the call stack — every frame \
    except the currently executing one (which ",
    .code "currentFrame",
    .plain " returns). Safe because the ",
    .code "Runnable",
    .plain " precondition guarantees the stack is non-empty."])
  (m "The machine state." : Machine)
  requires Runnable(m)
  : List StackFrame :=
    m↦thread↦stack·tail!

defFn evalConstant (.plain "evalConstant")
  (.plain "Convert a compile-time constant to a runtime value.")
  (cv "The constant value." : ConstValue)
  : Value where
  | .bool b => Value.bool‹b›
  | .int iv => Value.int‹iv›
  | .tuple es =>
      Value.tuple‹es ·map evalConstant›
  | .array es =>
      Value.array‹es ·map evalConstant›
  | .fnPtr name => Value.fnPtr‹name›

defFn typedLoad (.plain "typedLoad")
  (.seq [.plain "Load a value of the given type from \
    memory at the given pointer. Returns ", .code "None",
    .plain " if the pointer is invalid or the bytes \
    cannot be decoded."])
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (ty "The type to load." : Ty)
  : Option Value :=
    let sz ← Ty.bytes ‹ty› ;
    let rawBytes := Memory.load ‹m, ptr, sz› ;
    decode ‹ty, rawBytes›

defFn typedStore (.plain "typedStore")
  (.plain "Store a value into memory at the given pointer. \
   Encodes the value as bytes and writes them to memory.")
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (v "The value to store." : Value)
  : Memory :=
    Memory.store ‹m, ptr, encode ‹v››

defFn liveAndStoreArgs (.plain "liveAndStoreArgs")
  (.seq [.plain "Per-argument helper for ", .code "createFrame",
    .plain ": iterate the caller-provided value list with ",
    .code "k", .plain " tracking the current callee local \
    index (starting at 1 for the first argument). For each \
    value, allocate the local's backing storage via ",
    .code "StackFrame.storageLive",
    .plain " and write the value into that allocation with ",
    .code "typedStore",
    .plain ". The locals-map lookup is total because ",
    .code "StackFrame.storageLive",
    .plain " always inserts an entry for the local it was \
    just called with."])
  (args "The caller-provided argument values." : List Value)
  (k "The current callee local index." : Nat)
  (frame "The stack frame under construction." : StackFrame)
  (mem "The memory state." : Memory)
  : StackFrame × Memory where
  | [] ; _ ; frame ; mem => ⟨frame, mem⟩
  | v :: rest ; k ; frame ; mem =>
      let ⟨frame1, mem1⟩ :=
        StackFrame.storageLive ‹frame, mem, Local⟨k⟩› ;
      let ptr := mapAt ‹frame1↦locals, Local⟨k⟩› ;
      liveAndStoreArgs ‹rest, k + 1, frame1,
        typedStore ‹mem1, ptr, v››

defFn createFrame (.plain "createFrame")
  (.seq [.plain "Build a fresh stack frame for a call into ",
    .code "body", .plain " and push it onto the thread's \
    call stack. Allocates the return place (local 0) and \
    each argument local via ", .code "StackFrame.storageLive",
    .plain ", then writes the caller-provided argument \
    values into those allocations with ", .code "typedStore",
    .plain ". The program counter starts at statement 0 of \
    basic block 0. ABI, calling convention, and \
    stack-pop-action handling from MiniRust's ",
    .code "create_frame", .plain " are intentionally not \
    modelled here."])
  (m "The machine state." : Machine)
  (body "The function body being called." : Body)
  (args "The caller-provided argument values." : List Value)
  : Machine :=
    let initFrame := StackFrame⟨body,
      Location⟨BasicBlockIdx⟨0⟩, 0⟩, mapEmpty‹›⟩ ;
    let ⟨frame1, mem1⟩ := StackFrame.storageLive
      ‹initFrame, m↦mem, Local⟨0⟩› ;
    let ⟨frame2, mem2⟩ :=
      liveAndStoreArgs ‹args, 1, frame1, mem1› ;
    Machine⟨m↦program,
      Thread⟨frame2 :: m↦thread↦stack⟩,
      mem2⟩

defFn initialMachine (.plain "initialMachine")
  (.seq [.plain "Build the initial machine state for ",
    .code "program",
    .plain ": look up the start function body via ",
    .code "startProgram",
    .plain ", allocate an empty memory and thread, and push \
    an initial stack frame for the start body via ",
    .code "createFrame",
    .plain " with no caller-supplied argument values. The ",
    .code "validProgram",
    .plain " precondition guarantees the start function is \
    registered in the program. Mirrors MiniRust's ",
    .code "Machine::new",
    .plain ", with globals, function pointers, vtables, lock \
    state, additional threads, and I/O streams stripped — this \
    model is single-threaded and ignores those concerns."])
  (program "The program to initialise." : Program)
  requires validProgram(program)
  : Machine :=
    let body := Program.startProgram ‹program, lean_proof("h_validProgram")› ;
    let blank :=
      Machine⟨program, Thread⟨[]⟩, Memory⟨[]⟩⟩ ;
    createFrame ‹blank, body, []›

end Machine
