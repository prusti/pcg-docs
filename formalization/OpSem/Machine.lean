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
    (doc! "{m} is a runnable machine")
  long
    (doc! "the call stack of {m} is non-empty, the program of \
      {m} is valid, and the call stack of {m} is a valid \
      stack against the memory of {m}")
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

defFn prog (.plain "prog")
  (.seq [.plain "The program a machine state is executing. \
    Shorthand for the ", .code "program",
    .plain " field — used by top-level properties (",
    Doc.refLinkByName "Framing", .plain ", ",
    Doc.refLinkByName "NoAlias", .plain ", ",
    Doc.refLinkByName "Soundness",
    .plain ") to refer to the program implicitly carried by \
    the machine without a separate ", .code "pr",
    .plain " quantifier."])
  (m "The machine state." : Machine)
  : Program :=
    Program⟨m↦program↦functions, m↦program↦start⟩

defFn currentFrame (.plain "currentFrame")
  (doc! "The currently executing stack frame, i.e. the head \
    of the thread's call stack. Safe because the \
    `Runnable` precondition guarantees the stack is \
    non-empty.")
  (m "The machine state." : Machine)
  requires Runnable(m)
  : StackFrame :=
    m↦thread↦stack·head!

defFn currBody (.plain "currBody")
  (doc! "The body of the currently executing stack frame. Shorthand for `currentFrame`'s `body` \
    field; safe under the same `Runnable` precondition.")
  (m "The machine state." : Machine)
  requires Runnable(m)
  : Body :=
    (currentFrame ‹m, lean_proof("h_Runnable")›)↦body

defFn currPC (.plain "currPC")
  (doc! "The program counter of the currently executing stack frame. Shorthand for `currentFrame`'s \
    `pc` field; safe under the same `Runnable` precondition.")
  (m "The machine state." : Machine)
  requires Runnable(m)
  : Location :=
    (currentFrame ‹m, lean_proof("h_Runnable")›)↦pc

defFn stackTail (.plain "stackTail")
  (doc! "The tail of the call stack — every frame except the currently executing one (which \
    `currentFrame` returns). Safe because the `Runnable` precondition guarantees the stack is \
    non-empty.")
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
  (doc! "Load a value of the given type from memory at the given pointer. Returns `None` if the \
    pointer is invalid or the bytes cannot be decoded.")
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
  (doc! "Per-argument helper for `createFrame`: iterate the caller-provided value list with `k` \
    tracking the current callee local index (starting at 1 for the first argument). For each value, \
    allocate the local's backing storage via `StackFrame.storageLive` and write the value into that \
    allocation with `typedStore`. The locals-map lookup is total because `StackFrame.storageLive` \
    always inserts an entry for the local it was just called with.")
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
  (doc! "Build a fresh stack frame for a call into `body` and push it onto the thread's call stack. \
    Allocates the return place (local 0) and each argument local via `StackFrame.storageLive`, then \
    writes the caller-provided argument values into those allocations with `typedStore`. The program \
    counter starts at statement 0 of basic block 0. ABI, calling convention, and stack-pop-action \
    handling from MiniRust's `create_frame` are intentionally not modelled here.")
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
  (doc! "Build the initial machine state for `program`: look up the start function body via \
    `startProgram`, allocate an empty memory and thread, and push an initial stack frame for the \
    start body via `createFrame` with no caller-supplied argument values. The #validProgram \
    precondition guarantees the start function is registered in the program. Mirrors MiniRust's \
    `Machine::new`, with globals, function pointers, vtables, lock state, additional threads, and \
    I/O streams stripped — this model is single-threaded and ignores those concerns.")
  (program "The program to initialise." : Program)
  requires validProgram(program)
  : Machine :=
    let body := Program.startProgram ‹program, lean_proof("h_validProgram")› ;
    let blank :=
      Machine⟨program, Thread⟨[]⟩, Memory⟨[]⟩⟩ ;
    createFrame ‹blank, body, []›

end Machine
