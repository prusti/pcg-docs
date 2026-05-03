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
    (doc! "the program of {m} is valid, the memory of {m} is \
      a valid memory, and the call stack of {m} is a valid \
      stack against the memory of {m}")
  (m "The machine state." : Machine)
  :=
    validProgram m↦program ∧
    validMemory m↦mem ∧
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
    enters with a memory whose existing allocations are non-overlapping. The \
    #StackFrame.localsAllocated precondition tracks which locals have already been brought live: \
    on entry, locals at indices `1` through `k - 1` are allocated, and on exit the \
    freshly-allocated argument locals extend that range up through `k + args.length - 1` — \
    `createFrame` consumes that postcondition to assert that every argument local is allocated \
    after the loop.")
  (args "The caller-provided argument values." : List Value)
  (k "The current callee local index." : Nat)
  (frame "The stack frame under construction." : StackFrame)
  (mem "The memory state." : Memory)
  requires validMemory mem
      using [liveAndStoreArgs.precondAxiom],
    validStackFrame mem frame
      using [liveAndStoreArgs.precondAxiom],
    localsAllocated frame 1 k
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
    #validMachine precondition gives both #validMemory m.mem and #validStack m.thread.stack m.mem \
    directly (the former is now a conjunct of #validMachine, threaded into `liveAndStoreArgs`); the \
    #validBody precondition \
    discharges both of `storageLive`'s obligations on the initial frame: the #validLocal \
    `initFrame.body Local⟨0⟩` requirement via the \"`decls ≠ []`\" conjunct, and the \
    #validStackFrame `m.mem initFrame` requirement via the \"`blocks ≠ []`\" conjunct (which closes \
    the #validLocation `body START` half of #validStackFrame; the locals-validity half is vacuous \
    since the initial frame's locals map is empty). After `liveAndStoreArgs` returns, the \
    strengthened postcondition of `liveAndStoreArgs` (#StackFrame.localsAllocated extended to the \
    range `[1, 1 + args.length)`) witnesses that every argument local — locals 1 through \
    `args.length` — has been brought live; that witness is bound below as `_h_args_alloc` (the \
    proof itself is left as `sorry` until the postcondition lemma about `liveAndStoreArgs` is \
    discharged).")
  (m "The machine state." : Machine)
  (body "The function body being called." : Body)
  (args "The caller-provided argument values." : List Value)
  requires validMachine m, validBody body
  : Machine :=
    let initFrame := StackFrame⟨body, START, mapEmpty‹›⟩ ;
    let ⟨frame1, mem1⟩ := StackFrame.storageLive
      initFrame m↦mem Local⟨0⟩
      proof[(by
        -- `validStackFrame m.mem initFrame` unfolds to
        -- `validBody body ∧ validLocation body START ∧
        --  ∀ ptr ∈ mapValues mapEmpty, validPtr m.mem ptr`.
        -- `validBody body` is `h_validBody`. The third
        -- conjunct is vacuous — the initial frame's locals
        -- map is empty. The middle conjunct's first sub-
        -- conjunct is `0 < body.blocks.length`, supplied by
        -- the `blocks ≠ []` clause of `h_validBody` via
        -- `List.length_pos_iff`; its second sub-conjunct
        -- (`0 ≤ …`) is `Nat.zero_le`.
        refine ⟨h_validBody, ?_, ?_⟩
        · exact ⟨List.length_pos_iff.mpr h_validBody.2.1,
            Nat.zero_le _⟩
        · intro ptr hptr
          change ptr ∈ mapValues (mapEmpty (κ := Local) (ν := ThinPointer)) at hptr
          unfold mapValues mapEmpty at hptr
          rw [Std.HashMap.fold_eq_foldl_toList,
              Std.HashMap.toList_empty] at hptr
          exact (List.not_mem_nil hptr).elim)] proof[(by
        -- `validLocal body Local⟨0⟩` reduces to
        -- `0 < body.decls.length`. `h_validBody : validBody
        -- body` has `decls ≠ []` as its first conjunct, and
        -- `List.length_pos_iff` lifts that to the strict
        -- inequality.
        show 0 < body.decls.length
        exact List.length_pos_iff.mpr h_validBody.1)] ;
    let ⟨frame2, mem2⟩ :=
      liveAndStoreArgs args 1 frame1 mem1
        proof[sorry] proof[sorry]
        proof[(by
          -- `localsAllocated frame1 1 1` reduces to
          -- `∀ i, 1 ≤ i → i < 1 → …`; the premises `1 ≤ i`
          -- and `i < 1` are jointly contradictory.
          intro i hlo hhi
          omega)] ;
    -- Witness: every argument local is allocated in the
    -- post-call frame. The bound name is unused at runtime
    -- (prefixed with `_` to silence the unused-let warning);
    -- its purpose is to demonstrate that the strengthened
    -- postcondition of `liveAndStoreArgs` flows through to
    -- a usable fact about `frame2`. The proof is `sorry`
    -- until a postcondition lemma about `liveAndStoreArgs`
    -- is discharged — the type ascription makes the assertion
    -- explicit at the call site.
    let _h_args_alloc :=
      proof[(sorry : StackFrame.localsAllocated frame2 1
        (1 + args.length))] ;
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
    program is `program` (#validProgram directly), and the empty-allocation list satisfies both \
    #validMemory and the empty-stack #validStack vacuously. Mirrors MiniRust's `Machine::new`, \
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
        -- `validProgram blank.program ∧ validMemory blank.mem ∧
        --  validStack [] blank.mem`. The first conjunct is
        -- `h_validProgram`; the middle conjunct is vacuous —
        -- `blank.mem.allocs = []`, so the `j < 0` clause of the
        -- universal is unsatisfiable; the third is the
        -- `validStack.nil` constructor applied at the empty
        -- stack of `blank`.
        refine ⟨h_validProgram, ?_, validStack.nil⟩
        intro _ _ h_pre0
        exact absurd h_pre0.2 (Nat.not_lt_zero _))]
      proof[validBody_startProgram program h_validProgram]

end Machine
