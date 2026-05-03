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
    after the loop. The bound `k + args.length ≤ frame.body.decls.length` keeps the indices of the \
    locals about to be brought live in range so each `storageLive` call discharges its \
    #validLocal obligation; the bound is inductive across the recursive call (sum is preserved as \
    `args` shrinks and `k` grows). The recursive-call preconditions are discharged explicitly via \
    the `*_preserves_*` infrastructure in `OpSem/Memory.lean` and `OpSem/StackFrame.lean` rather \
    than going through a universal escape-hatch axiom.")
  (args "The caller-provided argument values." : List Value)
  (k "The current callee local index." : Nat)
  (frame "The stack frame under construction." : StackFrame)
  (mem "The memory state." : Memory)
  requires validMemory mem,
    validStackFrame mem frame,
    StackFrame.localsAllocated frame 1 k,
    k + args·length ≤ frame↦body↦decls·length
  : StackFrame × Memory where
  | [] ; _ ; frame ; mem => ⟨frame, mem⟩
  | v :: rest ; k ; frame ; mem =>
      -- `storageLive`'s `validStackFrame` arg is `h_validStackFrame`
      -- directly. Its `validLocal frame.body ⟨k⟩` arg unfolds to
      -- `k < frame.body.decls.length`, which follows from
      -- `h_pre3 : k + args.length ≤ frame.body.decls.length` once
      -- `args.length` is reduced via the arm pattern `args = v :: rest`.
      -- The result is bound to a single name and accessed through
      -- `Prod.fst` / `Prod.snd` (rather than a destructuring
      -- `let ⟨frame1, mem1⟩ :=`) so the recursive call's
      -- precondition proofs can rewrite `frame1` / `mem1` to the
      -- underlying `(storageLive …).fst` / `.snd` definitionally.
      let storageLiveResult := StackFrame.storageLive frame mem Local⟨k⟩
        proof[h_validStackFrame] proof[(by
          show k < frame.body.decls.length
          simp only [List.length_cons] at h_pre3
          omega)] ;
      let frame1 := Prod.fst storageLiveResult ;
      let mem1 := Prod.snd storageLiveResult ;
      let ptr := mapAt frame1↦locals Local⟨k⟩ ;
      liveAndStoreArgs rest (k + 1) frame1 (typedStore mem1 ptr v)
        proof[Memory.store_preserves_validMemory _ _ _
          (StackFrame.storageLive_preserves_validMemory _ _ _ _ _
            h_validMemory)]
        proof[StackFrame.validStackFrame_store_preserves _ _
          (StackFrame.storageLive_preserves_validStackFrame _ _ _ _ _)]
        proof[StackFrame.storageLive_localsAllocated_extend _ _
          h_pre2]
        proof[(by
          -- `frame1.body = frame.body` by the `@[simp]` lemma
          -- `storageLive_body`; once `frame1` and `storageLiveResult`
          -- are unfolded, that simp lemma reduces the goal's
          -- `.fst.body.decls.length` to `frame.body.decls.length`,
          -- and `omega` closes it from `h_pre3`.
          show (k + 1) + rest.length ≤ frame1.body.decls.length
          unfold frame1 storageLiveResult
          simp only [StackFrame.storageLive_body, List.length_cons] at h_pre3 ⊢
          omega)]

defRaw inFns =>
/-- Postcondition of `liveAndStoreArgs`: the returned frame has
    every local in the half-open range `[1, k + args.length)`
    allocated. The entry hypothesis `localsAllocated frame 1 k`
    is extended by the `args.length` consecutive `storageLive`
    calls inside the loop, each of which brings one more local
    live. Used by `createFrame` to witness that every
    argument local is allocated in the post-call frame.

    The predicate names are written unqualified so the same
    source resolves under both elaboration contexts: in-tree
    `StackFrame.validStackFrame` / `StackFrame.localsAllocated`
    via `open StackFrame`, and the generated module's
    `Memory.validStackFrame` / `StackFrame.localsAllocated`
    via the file-top `open Memory StackFrame`. -/
private theorem liveAndStoreArgs_localsAllocated
    (args : List Value) (k : Nat) (frame : StackFrame) (mem : Memory)
    (h1 : validMemory mem) (h2 : validStackFrame mem frame)
    (h3 : StackFrame.localsAllocated frame 1 k)
    (h4 : k + args.length ≤ frame.body.decls.length) :
    StackFrame.localsAllocated
      (liveAndStoreArgs args k frame mem h1 h2 h3 h4).fst
      1 (k + args.length) := by
  induction args generalizing k frame mem with
  | nil =>
    -- The `nil` arm of `liveAndStoreArgs` returns `(frame, mem)`
    -- definitionally; `unfold` exposes this so the goal reduces
    -- to `localsAllocated frame 1 (k + 0)`, matching `h3`.
    unfold liveAndStoreArgs
    rw [List.length_nil, Nat.add_zero]
    exact h3
  | cons v rest ih =>
    -- Re-shape the conclusion to match the IH's shape under the
    -- recursive call's `(k+1, frame1, ...)` arguments.
    have h_len : k + (v :: rest).length = (k + 1) + rest.length := by
      rw [List.length_cons]; omega
    rw [h_len]
    -- The cons branch reduces to a recursive call on
    -- `(rest, k+1, frame1, typedStore mem1 ptr v)` with axiom-
    -- derived precondition proofs. Apply the IH; proof
    -- irrelevance handles the precondition arguments.
    unfold liveAndStoreArgs
    apply ih

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
    `args.length` — has been brought live; that witness is bound below as `_h_args_alloc` and \
    discharged via #liveAndStoreArgs_localsAllocated.")
  (m "The machine state." : Machine)
  (body "The function body being called." : Body)
  (args "The caller-provided argument values." : List Value)
  requires validMachine m, validBody body, args·length ≤ body↦numArgs
  : Machine :=
    let initFrame := StackFrame⟨body, START, mapEmpty‹›⟩ ;
    -- `storageLive`'s result is bound to a single name and accessed
    -- through `Prod.fst` / `Prod.snd` (rather than a destructuring
    -- `let ⟨frame1, mem1⟩ :=`) so downstream proofs can rewrite
    -- `frame1` / `mem1` to the underlying `(storageLive …).fst` /
    -- `.snd` definitionally — pattern-bound variables compile to a
    -- `match` whose components are not zeta-reducible to projections
    -- at type-checking time.
    let storageLive_initLocal0 := StackFrame.storageLive
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
    let frame1 := Prod.fst storageLive_initLocal0 ;
    let mem1 := Prod.snd storageLive_initLocal0 ;
    let ⟨frame2, mem2⟩ :=
      liveAndStoreArgs args 1 frame1 mem1
        proof[StackFrame.storageLive_preserves_validMemory _ _ _ _ _
          h_validMachine.2.1]
        proof[StackFrame.storageLive_preserves_validStackFrame _ _ _ _ _]
        proof[(by
          -- `localsAllocated frame1 1 1` reduces to
          -- `∀ i, 1 ≤ i → i < 1 → …`; the premises `1 ≤ i`
          -- and `i < 1` are jointly contradictory.
          intro i hlo hhi
          omega)]
        proof[(by
          -- Discharge `1 + args.length ≤ frame1.body.decls.length`.
          -- Unfolding the local lets exposes
          -- `(StackFrame.storageLive initFrame _ _ _ _).fst.body`,
          -- which the `@[simp]` lemma `storageLive_body` collapses
          -- to `initFrame.body = body`. Then combine
          -- `h_pre2 : args.length ≤ body.numArgs` with
          -- `h_validBody.2.2.2.2 : body.numArgs < body.decls.length`.
          show 1 + args.length ≤ frame1.body.decls.length
          unfold frame1 storageLive_initLocal0 initFrame
          simp only [StackFrame.storageLive_body]
          have h_numArgs := h_validBody.2.2.2.2
          omega)] ;
    -- Witness: every argument local is allocated in the
    -- post-call frame. The bound name is unused at runtime
    -- (prefixed with `_` to silence the unused-let warning);
    -- its purpose is to demonstrate that the strengthened
    -- postcondition of `liveAndStoreArgs` flows through to
    -- a usable fact about `frame2`. Discharged via
    -- #liveAndStoreArgs_localsAllocated. The four precondition
    -- arguments mirror the proofs supplied to the
    -- `liveAndStoreArgs` call above, recomposed to match the
    -- postcondition lemma's parameter order — by proof
    -- irrelevance, the conclusion is independent of which proofs
    -- are supplied.
    let _h_args_alloc :=
      proof[liveAndStoreArgs_localsAllocated args 1 frame1 mem1
        (StackFrame.storageLive_preserves_validMemory _ _ _ _ _
          h_validMachine.2.1)
        (StackFrame.storageLive_preserves_validStackFrame _ _ _ _ _)
        (by intro i hlo hhi; omega)
        (by
          -- Mirrors the bound proof passed to `liveAndStoreArgs`
          -- above: unfold the local lets so `storageLive_body`
          -- can rewrite `frame1.body.decls.length` to
          -- `body.decls.length`, then close with `omega` from
          -- `h_pre2` and `h_validBody.2.2.2.2`.
          unfold frame1 storageLive_initLocal0 initFrame
          simp only [StackFrame.storageLive_body]
          have h_numArgs := h_validBody.2.2.2.2
          omega)] ;
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
        -- `validStack.nil` constructor.
        refine ⟨h_validProgram, ?_, validStack.nil⟩
        intro _ _ h
        exact absurd h.2 (Nat.not_lt_zero _))]
      proof[validBody_startProgram program h_validProgram]
      proof[Nat.zero_le _]

end Machine
