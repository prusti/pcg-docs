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
    `validStack` clause of `Runnable m`: every frame in the
    stack is `validStackFrame`, which includes
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
  exact (h_Runnable.2.2.1 callerFrame h_inStack).2.1

defRaw middle =>
open ThinPointer in
/-- Concatenation lemma for `localAllocations`: the
    allocations of a stack `head :: tail` decompose into
    `head`'s allocations followed by the rest of the stack's
    allocations. Used below to relate `validStack` on a stack
    to `validStack` on its tail. -/
private theorem localAllocations_cons (head : StackFrame)
    (tail : List StackFrame) (mem : Memory) :
    localAllocations (head :: tail) mem =
      ((mapValues head.locals).flatMap (fun ptr =>
        ptrAllocations ptr mem)) ++ localAllocations tail mem := by
  unfold localAllocations
  simp [List.flatMap]

defRaw middle =>
open ThinPointer in
/-- `Runnable` is preserved by popping the topmost stack
    frame, *provided* the resulting tail is non-empty. The
    popped state's stack is `stackTail m h_Runnable`; the
    `validProgram` and `validStack` clauses of `Runnable`
    transfer through the pop because nothing about the
    program or memory changes, and the tail is a sublist of
    the original stack. -/
theorem Machine.Runnable_after_pop
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (h_tailNonEmpty : Machine.stackTail m h_Runnable ≠ []) :
    Machine.Runnable
      { m with
        thread := ⟨Machine.stackTail m h_Runnable⟩ } := by
  refine ⟨h_tailNonEmpty, h_Runnable.2.1, ?_, ?_⟩
  · -- `forAll validStackFrame` on the tail follows from the
    -- same on the full stack.
    intro f hf
    -- `hf` arrives as `f ∈ ({ m with thread := ⟨stackTail …⟩ }).thread.stack`;
    -- the structure projection reduces, but only after we
    -- `change` past it.
    change f ∈ Machine.stackTail m h_Runnable at hf
    have h_inStack : f ∈ m.thread.stack := by
      unfold Machine.stackTail at hf
      match hstk : m.thread.stack, h_Runnable.1 with
      | [], hne => exact absurd rfl hne
      | hd :: tl, _ =>
        rw [hstk] at hf
        rw [List.tail!_cons] at hf
        exact List.mem_cons_of_mem hd hf
    exact h_Runnable.2.2.1 f h_inStack
  · -- Non-overlapping pairs in the tail's allocations follow
    -- from the same property on the full stack's allocations:
    -- the tail's allocations form the suffix of the original
    -- list, so every pair (i, j) in the tail corresponds to
    -- the pair (i + L, j + L) in the full list (where L is
    -- the head frame's allocation count) and the original
    -- non-overlapping property covers it.
    intro i j h_ij
    obtain ⟨hij, hjlen⟩ := h_ij
    -- The structure projection
    -- `({ … with thread := ⟨stackTail …⟩ }).thread.stack`
    -- reduces to `stackTail m h_Runnable` definitionally, so
    -- `change` lets us replace the bulky form in the goal and
    -- in `hjlen`.
    change j < (localAllocations
        (Machine.stackTail m h_Runnable) m.mem).length at hjlen
    change Allocation.nonOverlapping
        (localAllocations (Machine.stackTail m h_Runnable) m.mem)[i]!
        (localAllocations (Machine.stackTail m h_Runnable) m.mem)[j]!
      = true
    cases hstk : m.thread.stack with
    | nil => exact absurd hstk h_Runnable.1
    | cons hd tl =>
      have h_tail_eq : Machine.stackTail m h_Runnable = tl := by
        unfold Machine.stackTail; rw [hstk]; rfl
      rw [h_tail_eq] at hjlen ⊢
      let headAllocs :=
        (mapValues hd.locals).flatMap
          (fun ptr => ptrAllocations ptr m.mem)
      have h_concat : localAllocations m.thread.stack m.mem
          = headAllocs ++ localAllocations tl m.mem := by
        rw [hstk]; exact localAllocations_cons hd tl m.mem
      have h_full := h_Runnable.2.2.2
      have h_iL : i + headAllocs.length < j + headAllocs.length :=
        Nat.add_lt_add_right hij _
      have h_jL : j + headAllocs.length
          < (localAllocations m.thread.stack m.mem).length := by
        rw [h_concat, List.length_append]
        omega
      have h_pair := h_full _ _ ⟨h_iL, h_jL⟩
      -- Translate the indices in the concatenation back to tail
      -- indices: `(headAllocs ++ tailAllocs)[i + L]! = tailAllocs[i]!`.
      rw [h_concat] at h_pair
      have h_translate : ∀ (k : Nat),
          (headAllocs ++ localAllocations tl m.mem)[k + headAllocs.length]!
            = (localAllocations tl m.mem)[k]! := by
        intro k
        rw [List.getElem!_eq_getElem?_getD,
            List.getElem!_eq_getElem?_getD,
            List.getElem?_append_right (Nat.le_add_left _ _),
            Nat.add_sub_cancel]
      rw [h_translate, h_translate] at h_pair
      exact h_pair

defRaw middle =>
/-- `Runnable` is preserved by overwriting `m.mem` with a
    fresh `Memory`, *provided* the call stack is still valid
    against the new memory. The non-empty-stack and
    `validProgram` clauses of `Runnable` are unaffected by a
    memory swap; the precondition supplies the third clause
    directly. -/
theorem Machine.Runnable_after_mem_update
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (newMem : Memory)
    (h_validStack : validStack m.thread.stack newMem) :
    Machine.Runnable { m with mem := newMem } :=
  ⟨h_Runnable.1, h_Runnable.2.1, h_validStack⟩

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
                          -- The `validStack mPopped.thread.stack
                          -- mem'` obligation propagates to the
                          -- `Runnable_after_mem_update`
                          -- precondition. `placeStore` writes
                          -- bytes via `Memory.store`, which
                          -- preserves allocation count, addresses,
                          -- and data lengths, so `localAllocations`
                          -- is unchanged in shape and the
                          -- non-overlapping property carries
                          -- through. Discharging this rigorously
                          -- needs frame-preservation lemmas about
                          -- `Memory.store`; left as a sorry
                          -- alongside the existing sorries in
                          -- `OpSem/Step.lean`.
                          StepResult.ok (jumpToBlock
                            mWithMem nextBlock (proof[Machine.Runnable_after_mem_update
                                mPopped (Machine.Runnable_after_pop
                                  m h_Runnable
                                  (h_rest ▸ List.cons_ne_nil _ _)) mem'
                                  sorry]))
                      end
                  | _ => StepResult.done .error
                  end
              end
          end
      end

end Machine
