import OpSem.Memory
import OpSem.Program
import OpSem.PlacePtr
import OpSem.Thread
import OpSem.Value
import OpSem.Decode
import MIR.Body
import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw

-- Open `Memory` and `StackFrame` so the in-tree elaboration
-- of `liveAndStoreArgs`'s `validMemory` / `validStackFrame`
-- preconditions resolves them unqualified. (The Lean exporter
-- places these properties in `namespace Memory` /
-- `namespace StackFrame` respectively; both namespaces are
-- already opened in the generated file.)
open Memory StackFrame

defStruct Machine (.sym .mu, .text "Machine")
  "Machines"
  (doc! "A machine state \
    $μ ∈ _Machine_$ \
    bundles the whole program being executed, the \
    single-threaded execution context, and the shared memory. \
    Per-call state — the function body, program counter, and \
    local pointer map — lives on the thread's current stack \
    frame.")
where
  | program "The program being executed." : Program
  | thread "The single thread of execution." : Thread
  | mem "The memory." : Memory
  deriving Repr

namespace Machine

defProperty validMachine (.plain "validMachine")
  short
    (doc! "{m} is a valid machine")
  long
    (doc! "the program of {m} is valid, and the call stack of \
      {m} is a valid stack against the memory of {m}")
  (m "The machine state." : Machine)
  :=
    validProgram m↦program ∧
    validStack (m↦thread↦stack) m↦mem

defProperty Runnable (.plain "Runnable")
  short
    (doc! "{m} is a runnable machine")
  long
    (doc! "the call stack of {m} is non-empty and {m} is a \
      valid machine")
  (m "The machine state." : Machine)
  :=
    m↦thread↦stack ≠ [] ∧
    Machine.validMachine m

-- Source-only `Inhabited StackFrame` so `head!` inside
-- `currentFrame` (which relies on the precondition for
-- safety) elaborates against the source `defStruct`, which
-- only derives `Repr`. The Lean exporter adds `Inhabited`
-- automatically to the corresponding generated declaration,
-- so this is not re-emitted there.
private instance : Inhabited StackFrame :=
  ⟨⟨⟨[], 0, []⟩, ⟨⟨0⟩, 0⟩, ∅⟩⟩

defFn prog (.plain "prog")
  (doc! "The program a machine state is executing. \
    Shorthand for the `program` field — used by top-level \
    properties (#[Framing], #[NoAlias], #[Soundness]) to \
    refer to the program implicitly carried by the machine \
    without a separate `pr` quantifier.")
  (m "The machine state." : Machine)
  : Program :=
    Program⟨m↦program↦functions, m↦program↦start⟩

defFn currentFrame (.plain "currentFrame")
  (doc! "The currently executing stack frame, i.e. the head \
    of the thread's call stack. Safe because the \
    `Runnable` precondition guarantees the stack is \
    non-empty.")
  (m "The machine state." : Machine)
  requires Runnable m
  : StackFrame :=
    m↦thread↦stack·head!

defFn currBody (.plain "currBody")
  (doc! "The body of the currently executing stack frame. Shorthand for `currentFrame`'s `body` \
    field; safe under the same `Runnable` precondition.")
  (m "The machine state." : Machine)
  requires Runnable m
  : Body :=
    (currentFrame m proof[h_Runnable])↦body

defFn currPC (.plain "currPC")
  (doc! "The program counter of the currently executing stack frame. Shorthand for `currentFrame`'s \
    `pc` field; safe under the same `Runnable` precondition.")
  (m "The machine state." : Machine)
  requires Runnable m
  : Location :=
    (currentFrame m proof[h_Runnable])↦pc

defFn stackTail (.plain "stackTail")
  (doc! "The tail of the call stack — every frame except the currently executing one (which \
    `currentFrame` returns). Safe because the `Runnable` precondition guarantees the stack is \
    non-empty.")
  (m "The machine state." : Machine)
  requires Runnable m
  : List StackFrame :=
    m↦thread↦stack·tail!

defFn evalConstant (.plain "evalConstant")
  (.plain "Convert a compile-time constant to a runtime value.")
  (cv "The constant value." : ConstValue)
  : Value where
  | .bool b => Value.bool b
  | .int iv => Value.int iv
  | .tuple es =>
      Value.tuple (es ·map evalConstant)
  | .array es =>
      Value.array (es ·map evalConstant)
  | .fnPtr name => Value.fnPtr name

defFn typedLoad (.plain "typedLoad")
  (doc! "Load a value of the given type from memory at the given pointer. Returns `None` if the \
    pointer is invalid or the bytes cannot be decoded.")
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (ty "The type to load." : Ty)
  : Option Value :=
    let sz ← Ty.bytes ty ;
    let rawBytes := Memory.load m ptr sz ;
    decode ty rawBytes

defFn typedStore (.plain "typedStore")
  (.plain "Store a value into memory at the given pointer. \
   Encodes the value as bytes and writes them to memory.")
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (v "The value to store." : Value)
  : Memory :=
    Memory.store m ptr (encode v)

/-! `liveAndStoreArgs`'s recursive call needs to discharge
`validMemory` / `validStackFrame` for the post-`storageLive`,
post-`typedStore` memory and frame. Rigorous proofs need
`Memory.allocate` / `Memory.store` frame-preservation lemmas
(allocation count, addresses, data lengths preserved when
writing in-bounds); they are stubbed with `sorry` here. The
helper `liveAndStoreArgs.precondAxiom` takes any `Prop` and
returns a proof — `apply`'d by the DSL-generated
auto-discharge tactic, it closes the recursive-call
preconditions in one step (with sorry). -/

defRaw middle =>
private theorem liveAndStoreArgs.precondAxiom
    {P : Prop} : P := sorry

defFn liveAndStoreArgs (.plain "liveAndStoreArgs")
  (doc! "Per-argument helper for `createFrame`: iterate the caller-provided value list with `k` \
    tracking the current callee local index (starting at 1 for the first argument). For each value, \
    allocate the local's backing storage via `StackFrame.storageLive` and write the value into that \
    allocation with `typedStore`. The `validStackFrame` precondition discharges the same-named \
    obligation on `storageLive`; the `validMemory` precondition is structural — `liveAndStoreArgs` \
    enters with a memory whose existing allocations are non-overlapping.")
  (args "The caller-provided argument values." : List Value)
  (k "The current callee local index." : Nat)
  (frame "The stack frame under construction." : StackFrame)
  (mem "The memory state." : Memory)
  requires validMemory mem
      using [liveAndStoreArgs.precondAxiom],
    validStackFrame mem frame
      using [liveAndStoreArgs.precondAxiom]
  : StackFrame × Memory where
  | [] ; _ ; frame ; mem => ⟨frame, mem⟩
  | v :: rest ; k ; frame ; mem =>
      -- The `validStackFrame mem frame` precondition discharges
      -- `storageLive`'s first arg directly. The second arg
      -- (`validLocal frame.body ⟨k⟩`) needs a
      -- `k < frame.body.decls.length` bound that no precondition
      -- currently provides — left as `sorry` until a
      -- `args.length + k ≤ body.decls.length`-style invariant
      -- propagates from `createFrame`.
      let ⟨frame1, mem1⟩ := StackFrame.storageLive frame mem Local⟨k⟩
        proof[h_validStackFrame] proof[sorry] ;
      let ptr := mapAt frame1↦locals Local⟨k⟩ ;
      liveAndStoreArgs rest (k + 1) frame1 (typedStore mem1 ptr v)

defFn createFrame (.plain "createFrame")
  (doc! "Build a fresh stack frame for a call into `body` and push it onto the thread's call stack. \
    Allocates the return place (local 0) and each argument local via `StackFrame.storageLive`, then \
    writes the caller-provided argument values into those allocations with `typedStore`. The program \
    counter starts at #START — statement 0 of basic block 0. ABI, calling convention, and \
    stack-pop-action handling from MiniRust's `create_frame` are intentionally not modelled here. The \
    #validMachine precondition gives #validStack m.thread.stack m.mem (carrying enough non-overlap \
    structure to thread #validMemory m.mem into `liveAndStoreArgs`); the #validBody precondition \
    discharges `storageLive`'s #validLocal `initFrame.body Local⟨0⟩` requirement via the \
    #validBody \"`decls ≠ []`\" conjunct. The remaining #validStackFrame and #validLocation \
    `body START` obligations needed for the initial-frame construction are left as `sorry` for now.")
  (m "The machine state." : Machine)
  (body "The function body being called." : Body)
  (args "The caller-provided argument values." : List Value)
  requires validMachine m, validBody body
  : Machine :=
    let initFrame := StackFrame⟨body, START, mapEmpty‹›⟩ ;
    let ⟨frame1, mem1⟩ := StackFrame.storageLive
      initFrame m↦mem Local⟨0⟩
      proof[sorry] proof[(by
        -- `validLocal body Local⟨0⟩` reduces to
        -- `0 < body.decls.length`. `h_validBody : validBody
        -- body` has `decls ≠ []` as its first conjunct, and
        -- `List.length_pos_iff` lifts that to the strict
        -- inequality.
        show 0 < body.decls.length
        exact List.length_pos_iff.mpr h_validBody.1)] ;
    let ⟨frame2, mem2⟩ :=
      liveAndStoreArgs args 1 frame1 mem1
        proof[sorry] proof[sorry] ;
    Machine⟨m↦program,
      Thread⟨frame2 :: m↦thread↦stack⟩,
      mem2⟩

defFn initialMachine (.plain "initialMachine")
  (doc! "Build the initial machine state for `program`: look up the start function body via \
    `startProgram`, allocate an empty memory and thread, and push an initial stack frame for the \
    start body via `createFrame` with no caller-supplied argument values. The #validProgram \
    precondition guarantees the start function is registered in the program *and* that its body is \
    valid; the latter discharges `createFrame`'s #validBody precondition via \
    `validBody_startProgram`. The blank machine state vacuously satisfies #validMachine — its \
    program is `program` (#validProgram directly), and the empty-stack #validStack forall and \
    pairwise-non-overlap clauses are vacuously true. Mirrors MiniRust's `Machine::new`, \
    with globals, function pointers, vtables, lock state, additional threads, and I/O streams \
    stripped — this model is single-threaded and ignores those concerns.")
  (program "The program to initialise." : Program)
  requires validProgram program
  : Machine :=
    let body := Program.startProgram program proof[h_validProgram] ;
    let blank :=
      Machine⟨program, Thread⟨[]⟩, Memory⟨[]⟩⟩ ;
    createFrame blank body []
      proof[(by
        -- `validMachine blank` unfolds to
        -- `validProgram blank.program ∧ validStack [] blank.mem`.
        -- The first is `h_validProgram`; the second's two
        -- conjuncts (`forAll` over `[]`, and the pairwise
        -- non-overlap quantifier whose universe is `[]`) are
        -- both vacuously true.
        refine ⟨h_validProgram, ?_, ?_⟩
        · intro f hf
          exact absurd hf (List.not_mem_nil)
        · intro i j h_ij
          exact absurd h_ij.2 (Nat.not_lt_zero _))]
      proof[validBody_startProgram program h_validProgram]

end Machine
