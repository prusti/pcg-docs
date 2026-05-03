import Core.Dsl.DefFn
import Core.Dsl.DefRaw
import MIR.StmtOrTerminator
import OpSem.Expressions.Place
import OpSem.Machine
import OpSem.Statements
import OpSem.StepResult

defFn caseTarget (.plain "caseTarget")
  (doc! "Look up the basic block that a `switchInt` terminator should jump to when its operand \
    evaluates to `iv`. Scans the `cases` list in order for the first pair whose first component is \
    `iv`; returns the supplied `fallback` when no case matches. Mirrors MiniRust's \
    `cases.get(value).unwrap_or(fallback)`.")
  (cases "The case list of (value, target-block) pairs."
      : List (IntValue × BasicBlockIdx))
  (iv "The integer the operand evaluated to." : IntValue)
  (fallback "The default block when no case matches."
      : BasicBlockIdx)
  : BasicBlockIdx where
  | [] ; _ ; fallback => fallback
  | ⟨v, bb⟩ :: rest ; iv ; fallback =>
      if v == iv then bb
      else caseTarget rest iv fallback

namespace Machine

defFn fnFromPtr (.plain "fnFromPtr")
  (doc! "Resolve a function-pointer #Value against the machine's program: `Value.fnPtr name` looks \
    `name` up in `program.functions` and returns the matching #Body. Returns `None` for any other \
    value (the callee operand did not evaluate to a function pointer) or when the name is absent \
    from the program. Mirrors MiniRust's `fn_from_ptr`.")
  (m "The machine state." : Machine)
  (v "The value to interpret as a function pointer." : Value)
  : Option Body where
  | m ; .fnPtr name => mapGet (m↦program↦functions) name
  | _ ; _ => None

-- A body resolved through `fnFromPtr` is one of the bodies
-- registered in the program's function map, so the
-- whole-program `validProgram` invariant — projected through
-- `Runnable` — gives `validBody` directly. Used to discharge
-- `createFrame`'s `validBody` precondition at the `.call`
-- terminator's call site below; emitted via `defRaw inFns`
-- so it lands between `fnFromPtr` and `evalTerminator` in the
-- generated module rather than after every `defFn`.
defRaw inFns =>
theorem validBody_of_fnFromPtr_eq_some
    (m : Machine) (h_R : Machine.Runnable m)
    (v : Value) (b : Body)
    (h : Machine.fnFromPtr m v = some b) :
    validBody b := by
  cases v with
  | fnPtr name =>
    -- `Machine.fnFromPtr m (.fnPtr name)` reduces to
    -- `mapGet m.program.functions name`, so `h` directly
    -- witnesses membership in `mapValues`.
    unfold Machine.fnFromPtr at h
    exact h_R.2.1.2 b (mem_mapValues_of_mapGet_eq_some h)
  | bool _ | int _ | tuple _ | array _ | ptr _ =>
    -- Non-`fnPtr` values fall into the catch-all `none`
    -- branch of `Machine.fnFromPtr`, contradicting
    -- `… = some b`.
    all_goals (unfold Machine.fnFromPtr at h; simp at h)

defFn evalArgs (.plain "evalArgs")
  (doc! "Evaluate a list of operand arguments left-to-right. Returns `Some` of the resulting value \
    list when every operand evaluates successfully, `None` as soon as any operand fails. Used by the \
    `call` terminator to gather the values to pass to a callee.")
  (m "The machine state." : Machine)
  (args "The argument operands." : List Operand)
  requires Runnable m
  : Option (List Value) where
  | _ ; [] => Some []
  | m ; a :: rest =>
      let v ← evalOperand
        m a proof[h_Runnable] ;
      let vs ← evalArgs m rest ;
      Some (v :: vs)

defFn jumpToBlock (.plain "jumpToBlock")
  (doc! "Set the current frame's program counter to statement 0 of `target`, leaving the rest of \
    the call stack and memory unchanged. Mirrors MiniRust's `jump_to_block`.")
  (m "The machine state." : Machine)
  (target "The basic block to jump to." : BasicBlockIdx)
  requires Runnable m
  : Machine :=
    let frame := currentFrame
      m proof[h_Runnable] ;
    let rest := stackTail
      m proof[h_Runnable] ;
    let newPc := Location⟨target, 0⟩ ;
    let newFrame := frame[pc => newPc] ;
    m[thread => Thread⟨newFrame :: rest⟩]

-- The `.return_` branch of `evalTerminator` performs a stack
-- pop and a memory update; the called helpers
-- (`getStmtOrTerminator`, `evalPlace`, `jumpToBlock`) need
-- preconditions that are not directly in scope as DSL
-- hypotheses. The three theorems below name the missing
-- obligations explicitly so the call sites can pass named
-- proofs. Each one strengthens the previous `axiom`
-- formulation with the additional hypothesis that makes it
-- actually true (the originals were universally quantified
-- with no link to the data they should depend on).

defRaw middle =>
/-- A stack frame that lives in the tail of `m`'s call stack
    has a valid program counter in its body. Follows from the
    `validStack` clause of `Runnable m` via
    `validStack.frame_valid`: every frame in the stack is
    `validStackFrame`, which includes
    `validLocation frame.body frame.pc`. -/
theorem Machine.tailFrame_validLocation
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (callerFrame : StackFrame)
    (h_mem : callerFrame ∈ Machine.stackTail m h_Runnable) :
    validLocation callerFrame.body callerFrame.pc := by
  -- `stackTail m h_Runnable` unfolds to `m.thread.stack.tail!`.
  -- For a non-empty stack (guaranteed by `Runnable`'s first
  -- conjunct), `tail!_cons` rewrites it to the regular tail,
  -- so any frame in the tail is also in the original stack.
  have h_inStack : callerFrame ∈ m.thread.stack := by
    unfold Machine.stackTail at h_mem
    match hstk : m.thread.stack, h_Runnable.1 with
    | [], hne => exact absurd rfl hne
    | hd :: tl, _ =>
      rw [hstk] at h_mem
      rw [List.tail!_cons] at h_mem
      exact List.mem_cons_of_mem hd h_mem
  exact (validStack.frame_valid h_Runnable.2.2.2 h_inStack).2.1

defRaw middle =>
/-- `Runnable` is preserved by popping the topmost stack
    frame, *provided* the resulting tail is non-empty. The
    popped state's stack is `stackTail m h_Runnable`; the
    `validProgram` and `validStack` clauses of `Runnable`
    transfer through the pop because nothing about the
    program or memory changes, and the new inductive
    `validStack` exposes the tail's `validStack` directly via
    `validStack.tail` after destructuring the original cons
    case. -/
theorem Machine.Runnable_after_pop
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (h_tailNonEmpty : Machine.stackTail m h_Runnable ≠ []) :
    Machine.Runnable
      { m with
        thread := ⟨Machine.stackTail m h_Runnable⟩ } := by
  refine ⟨h_tailNonEmpty, h_Runnable.2.1, h_Runnable.2.2.1, ?_⟩
  -- The new state's `thread.stack` projects to
  -- `Machine.stackTail m h_Runnable`; reduce the bulky
  -- `{ … with … }.thread.stack` form first.
  change validStack (Machine.stackTail m h_Runnable) m.mem
  -- The original stack must be `head :: tail`; expose that
  -- shape so we can apply `validStack.tail` to the cons-shaped
  -- witness `h_Runnable.2.2.2 : validStack m.thread.stack m.mem`.
  cases hstk : m.thread.stack with
  | nil => exact absurd hstk h_Runnable.1
  | cons hd tl =>
    have h_tail_eq : Machine.stackTail m h_Runnable = tl := by
      unfold Machine.stackTail; rw [hstk]; rfl
    rw [h_tail_eq]
    have h_vs := h_Runnable.2.2.2
    rw [hstk] at h_vs
    exact h_vs.tail

defRaw middle =>
/-- `Runnable` is preserved by overwriting `m.mem` with a
    fresh `Memory`, *provided* the new memory is itself valid
    and the call stack is still valid against it. The
    non-empty-stack and `validProgram` clauses of `Runnable`
    are unaffected by a memory swap; the two preconditions
    supply the `validMemory` and `validStack` clauses
    directly. -/
theorem Machine.Runnable_after_mem_update
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (newMem : Memory)
    (h_validMemory : Memory.validMemory newMem)
    (h_validStack : validStack m.thread.stack newMem) :
    Machine.Runnable { m with mem := newMem } :=
  ⟨h_Runnable.1, h_Runnable.2.1, h_validMemory, h_validStack⟩

defRaw middle =>
/-- `placeStore` preserves `validMemory`: it delegates to
    `typedStore`, which is `Memory.store` on the place's thin
    pointer with `encode v` as the byte payload. Discharged by
    `Memory.store_preserves_validMemory`. -/
theorem Machine.placeStore_preserves_validMemory
    (m : Memory) (pp : PlacePtr) (v : Value) :
    Memory.validMemory m → Memory.validMemory (placeStore m pp v) := by
  unfold placeStore typedStore
  exact Memory.store_preserves_validMemory _ _ _

defRaw middle =>
/-- `placeStore` preserves `validStack`: it delegates to
    `typedStore`, which is `Memory.store` on the place's thin
    pointer with `encode v` as the byte payload. Discharged by
    `validStack.store_preserves`. -/
theorem Machine.placeStore_preserves_validStack
    (stack : List StackFrame) (m : Memory)
    (pp : PlacePtr) (v : Value) :
    validStack stack m → validStack stack (placeStore m pp v) := by
  unfold placeStore typedStore
  exact validStack.store_preserves _ _

defFn evalTerminator (.plain "evalTerminator")
  (doc! "Evaluate a basic block terminator. The terminator is responsible for advancing the program \
    counter — including switching to a new basic block when appropriate. `goto` jumps to its target \
    block via `jumpToBlock`; `drop` jumps to its successor without modelling drop semantics; \
    `unreachable` halts with `error`; `switchInt` evaluates its operand and jumps to the \
    case-matching basic block, falling back to the terminator's `fallback` when no case matches \
    (mirrors MiniRust's `Terminator::Switch`); `call` evaluates the callee operand to a function \
    pointer via `evalOperand`, resolves it against the program's function map via `fnFromPtr`, \
    evaluates each argument operand via `evalArgs`, and pushes a fresh frame onto the thread stack \
    via `createFrame`. The caller's program counter is left pointing at the call terminator so the \
    matching `return` can recover the destination place and successor block when the callee returns. \
    ABI-compatibility checks from MiniRust's `Terminator::Call` are intentionally not modelled. \
    `return` loads the return value out of the callee's return slot (local 0), pops the callee \
    frame, and — when the call stack still contains a caller — looks at the caller's pending call \
    terminator to recover the destination place and successor block, stores the return value into \
    the destination, and jumps the caller to that block. When the popped frame was the bottom of the \
    stack, the program halts with `success`.")
  (m "The machine state." : Machine)
  (t "The terminator to evaluate." : Terminator)
  requires Runnable m
  : StepResult where
  | m ; .goto target =>
      StepResult.ok (jumpToBlock
        m target proof[h_Runnable])
  | _ ; .unreachable => StepResult.done .error
  | m ; .drop _ target =>
      StepResult.ok (jumpToBlock
        m target proof[h_Runnable])
  | m ; .switchInt op cases fallback =>
      match evalOperand
          m op proof[h_Runnable] with
      | .some (.int iv) =>
          let target := caseTarget cases iv fallback ;
          StepResult.ok (jumpToBlock
            m target proof[h_Runnable])
      | _ => StepResult.done .error
      end
  | m ; .call calleeOp args _ _ =>
      match evalOperand
          m calleeOp proof[h_Runnable] with
      | .none => StepResult.done .error
      | .some calleeVal =>
          match h_fnFrom : fnFromPtr m calleeVal with
          | .none => StepResult.done .error
          | .some calleeBody =>
              match evalArgs
                  m args proof[h_Runnable] with
              | .none => StepResult.done .error
              | .some argVals =>
                  StepResult.ok (createFrame
                    m calleeBody argVals
                    proof[h_Runnable.2]
                    proof[validBody_of_fnFromPtr_eq_some
                      m h_Runnable calleeVal calleeBody
                      h_fnFrom])
              end
          end
      end
  | m ; .return_ =>
      let frame := currentFrame
        m proof[h_Runnable] ;
      let retTy := frame↦body↦decls ! 0 ;
      match mapGet frame↦locals Local⟨0⟩ with
      | .none => StepResult.done .error
      | .some retPtr =>
          match typedLoad m↦mem retPtr retTy with
          | .none => StepResult.done .error
          | .some retVal =>
              -- Match directly on `stackTail …` (rather than a
              -- `let`-bound name) so the captured equation
              -- `h_rest` discharges the `Runnable_after_pop` /
              -- `tailFrame_validLocation` preconditions
              -- without `▸` running into the `let` indirection.
              match h_rest : stackTail m proof[h_Runnable] with
              | [] => StepResult.done .success
              | callerFrame :: _ =>
                  match getStmtOrTerminator
                      callerFrame↦body callerFrame↦pc (proof[Machine.tailFrame_validLocation
                          m h_Runnable callerFrame
                          (h_rest ▸ List.mem_cons_self)]) with
                  | .terminator (.call _ _ targetPlace
                      nextBlock) =>
                      let mPopped :=
                        m[thread => Thread⟨stackTail
                          m proof[h_Runnable]⟩] ;
                      match evalPlace
                          mPopped targetPlace (proof[Machine.Runnable_after_pop
                              m h_Runnable
                              (h_rest ▸ List.cons_ne_nil _ _)]) with
                      | .none => StepResult.done .error
                      | .some ⟨pp, _⟩ =>
                          let mem' := placeStore
                            mPopped↦mem pp retVal ;
                          let mWithMem :=
                            mPopped[mem => mem'] ;
                          -- `placeStore` writes bytes via
                          -- `Memory.store`, which preserves
                          -- allocation count, addresses, and (under
                          -- `canAccess`) data lengths, so
                          -- `localAllocations` is unchanged in shape
                          -- and the non-overlapping property carries
                          -- through. The two
                          -- `placeStore_preserves_*` lemmas package
                          -- the `validMemory` / `validStack`
                          -- preservation, each delegating to the
                          -- underlying `Memory.store_*` lemma.
                          StepResult.ok (jumpToBlock
                            mWithMem nextBlock (proof[Machine.Runnable_after_mem_update
                                mPopped (Machine.Runnable_after_pop
                                  m h_Runnable
                                  (h_rest ▸ List.cons_ne_nil _ _)) mem'
                                  (Machine.placeStore_preserves_validMemory
                                    _ _ _ h_Runnable.2.2.1)
                                  (Machine.placeStore_preserves_validStack
                                    _ _ _ _ (Machine.Runnable_after_pop
                                      m h_Runnable
                                      (h_rest ▸ List.cons_ne_nil _ _)).2.2.2)]))
                      end
                  | _ => StepResult.done .error
                  end
              end
          end
      end

end Machine
