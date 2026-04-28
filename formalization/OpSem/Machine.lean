import OpSem.Memory
import OpSem.Program
import OpSem.RuntimePlace
import OpSem.Thread
import OpSem.Value
import OpSem.Decode
import MIR.Body
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct Machine (.raw "\\mu", .doc (.plain "Machine"))
  "Machines"
  (.seq [
    .plain "A machine state ",
    Doc.defMath (.raw "\\mu") (.doc (.plain "Machine")),
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

defProperty RunnableMachine (.plain "RunnableMachine")
  short (mDoc) =>
    (.seq [mDoc, .plain " is a runnable machine"])
  long (mDoc) =>
    (.seq [.plain "the call stack of ", mDoc,
           .plain " is non-empty, the program of ", mDoc,
           .plain " is valid, and every stack frame on the \
           call stack of ", mDoc, .plain " is valid"])
  (m "The machine state." : Machine)
  :=
    m↦thread↦stackFrames ≠ [] ∧
    validProgram ‹m↦program› ∧
    m↦thread↦stackFrames·forAll fun frame =>
      validStackFrame ‹frame›

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
    `RunnableMachine` precondition guarantees the stack is \
    non-empty.")
  (m "The machine state." : Machine)
  requires RunnableMachine(m)
  : StackFrame :=
    m↦thread↦stackFrames·head!

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
    .code "typedStore", .plain ". Returns ", .code "None",
    .plain " if any allocation fails."])
  (args "The caller-provided argument values." : List Value)
  (k "The current callee local index." : Nat)
  (frame "The stack frame under construction." : StackFrame)
  (mem "The memory state." : Memory)
  : Option (StackFrame × Memory) where
  | [] ; _ ; frame ; mem => Some ⟨frame, mem⟩
  | v :: rest ; k ; frame ; mem =>
      let ⟨frame1, mem1⟩ ←
        StackFrame.storageLive ‹frame, mem, Local⟨k⟩› ;
      let ptr ← mapGet ‹frame1↦locals, Local⟨k⟩› ;
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
    basic block 0. Returns ", .code "None",
    .plain " if any allocation fails. ABI, calling \
    convention, and stack-pop-action handling from MiniRust's ",
    .code "create_frame", .plain " are intentionally not \
    modelled here."])
  (m "The machine state." : Machine)
  (body "The function body being called." : Body)
  (args "The caller-provided argument values." : List Value)
  : Option Machine :=
    let initFrame := StackFrame⟨body,
      Location⟨BasicBlockIdx⟨0⟩, 0⟩, mapEmpty‹›⟩ ;
    let ⟨frame1, mem1⟩ ← StackFrame.storageLive
      ‹initFrame, m↦mem, Local⟨0⟩› ;
    let ⟨frame2, mem2⟩ ←
      liveAndStoreArgs ‹args, 1, frame1, mem1› ;
    Some Machine⟨m↦program,
      Thread⟨frame2 :: m↦thread↦stackFrames⟩,
      mem2⟩

defFn initialMachine (.plain "initialMachine")
  (.seq [.plain "Build the initial machine state for ",
    .code "program",
    .plain ": look up the start function body, allocate an \
    empty memory and thread, and push an initial stack frame \
    for the start body via ", .code "createFrame",
    .plain " with no caller-supplied argument values. Mirrors \
    MiniRust's ", .code "Machine::new",
    .plain ", with globals, function pointers, vtables, lock \
    state, additional threads, and I/O streams stripped — this \
    model is single-threaded and ignores those concerns. \
    Returns ", .code "None",
    .plain " when the program's start function isn't in its \
    function map or when frame construction fails."])
  (program "The program to initialise." : Program)
  : Option Machine :=
    let body ← mapGet ‹program↦functions, program↦start› ;
    let blank :=
      Machine⟨program, Thread⟨[]⟩, Memory⟨[]⟩⟩ ;
    createFrame ‹blank, body, []›

end Machine
