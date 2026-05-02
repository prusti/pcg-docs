import Core.Dsl.DefFn
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
      else caseTarget ‹rest, iv, fallback›

namespace Machine

defFn fnFromPtr (.plain "fnFromPtr")
  (doc! "Resolve a function-pointer #Value against the machine's program: `Value.fnPtr name` looks \
    `name` up in `program.functions` and returns the matching #Body. Returns `None` for any other \
    value (the callee operand did not evaluate to a function pointer) or when the name is absent \
    from the program. Mirrors MiniRust's `fn_from_ptr`.")
  (m "The machine state." : Machine)
  (v "The value to interpret as a function pointer." : Value)
  : Option Body where
  | m ; .fnPtr name => mapGet ‹m↦program↦functions, name›
  | _ ; _ => None

defFn evalArgs (.plain "evalArgs")
  (doc! "Evaluate a list of operand arguments left-to-right. Returns `Some` of the resulting value \
    list when every operand evaluates successfully, `None` as soon as any operand fails. Used by the \
    `call` terminator to gather the values to pass to a callee.")
  (m "The machine state." : Machine)
  (args "The argument operands." : List Operand)
  requires Runnable(m)
  : Option (List Value) where
  | _ ; [] => Some []
  | m ; a :: rest =>
      let v ← evalOperand
        ‹m, a, proof[h_Runnable]› ;
      let vs ← evalArgs ‹m, rest› ;
      Some (v :: vs)

defFn jumpToBlock (.plain "jumpToBlock")
  (doc! "Set the current frame's program counter to statement 0 of `target`, leaving the rest of \
    the call stack and memory unchanged. Mirrors MiniRust's `jump_to_block`.")
  (m "The machine state." : Machine)
  (target "The basic block to jump to." : BasicBlockIdx)
  requires Runnable(m)
  : Machine :=
    let frame := currentFrame
      ‹m, proof[h_Runnable]› ;
    let rest := stackTail
      ‹m, proof[h_Runnable]› ;
    let newPc := Location⟨target, 0⟩ ;
    let newFrame := frame[pc => newPc] ;
    m[thread => Thread⟨newFrame :: rest⟩]

-- The `.return_` branch of `evalTerminator` performs a stack
-- pop and a memory update; the called helpers
-- (`getStmtOrTerminator`, `evalPlace`, `jumpToBlock`) need
-- preconditions that are not directly in scope as DSL
-- hypotheses. The three axioms below name the missing
-- obligations explicitly so the inline `proof[sorry]`
-- placeholders can be replaced with named references; each
-- axiom follows from the layout invariants encoded in
-- `Runnable` / `validStack` / `validStackFrame` but a full
-- DSL-level derivation would be intricate. Future work:
-- discharge these axioms with proper proofs.

defRaw middle =>
/-- The frame at the head of `m`'s call-stack tail (i.e. the
    caller frame visible to the popped state) has a valid
    program counter in its body. Follows from the
    `validStack` clause of `Runnable m` — every frame in the
    stack is `validStackFrame`, which includes
    `validLocation frame.body frame.pc`. -/
axiom Machine.tailFrame_validLocation
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (callerFrame : StackFrame) :
    validLocation callerFrame.body callerFrame.pc

defRaw middle =>
/-- `Runnable` is preserved by popping the topmost stack
    frame. The popped state's stack is `stackTail m
    h_Runnable`; the caller is responsible for ensuring this
    tail is non-empty (so the popped state still satisfies
    the non-empty-stack clause of `Runnable`). -/
axiom Machine.Runnable_after_pop
    (m : Machine) (h_Runnable : Machine.Runnable m) :
    Machine.Runnable
      { m with
        thread := ⟨Machine.stackTail m h_Runnable⟩ }

defRaw middle =>
/-- `Runnable` is preserved by overwriting `m.mem` with a
    fresh `Memory`. Holds when the new memory still satisfies
    `validStack m.thread.stack newMem` — the layout of the
    locals in the call stack must remain non-overlapping in
    the updated memory, which is the case when the update
    came from `placeStore` into a place backed by an
    allocation already on the stack. -/
axiom Machine.Runnable_after_mem_update
    (m : Machine) (h_Runnable : Machine.Runnable m)
    (newMem : Memory) :
    Machine.Runnable { m with mem := newMem }

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
  requires Runnable(m)
  : StepResult where
  | m ; .goto target =>
      StepResult.ok‹jumpToBlock
        ‹m, target, proof[h_Runnable]››
  | _ ; .unreachable => StepResult.done‹.error›
  | m ; .drop _ target =>
      StepResult.ok‹jumpToBlock
        ‹m, target, proof[h_Runnable]››
  | m ; .switchInt op cases fallback =>
      match evalOperand
          ‹m, op, proof[h_Runnable]› with
      | .some (.int iv) =>
          let target := caseTarget ‹cases, iv, fallback› ;
          StepResult.ok‹jumpToBlock
            ‹m, target, proof[h_Runnable]››
      | _ => StepResult.done‹.error›
      end
  | m ; .call calleeOp args _ _ =>
      match evalOperand
          ‹m, calleeOp, proof[h_Runnable]› with
      | .none => StepResult.done‹.error›
      | .some calleeVal =>
          match fnFromPtr ‹m, calleeVal› with
          | .none => StepResult.done‹.error›
          | .some calleeBody =>
              match evalArgs
                  ‹m, args, proof[h_Runnable]› with
              | .none => StepResult.done‹.error›
              | .some argVals =>
                  StepResult.ok‹createFrame
                    ‹m, calleeBody, argVals››
              end
          end
      end
  | m ; .return_ =>
      let frame := currentFrame
        ‹m, proof[h_Runnable]› ;
      let retTy := frame↦body↦decls ! 0 ;
      match mapGet ‹frame↦locals, Local⟨0⟩› with
      | .none => StepResult.done‹.error›
      | .some retPtr =>
          match typedLoad ‹m↦mem, retPtr, retTy› with
          | .none => StepResult.done‹.error›
          | .some retVal =>
              let rest := stackTail
                ‹m, proof[h_Runnable]› ;
              match rest with
              | [] => StepResult.done‹.success›
              | callerFrame :: _ =>
                  match getStmtOrTerminator
                      ‹callerFrame↦body, callerFrame↦pc,
                        proof[Machine.tailFrame_validLocation
                          m h_Runnable callerFrame]› with
                  | .terminator (.call _ _ targetPlace
                      nextBlock) =>
                      let mPopped :=
                        m[thread => Thread⟨rest⟩] ;
                      match evalPlace
                          ‹mPopped, targetPlace,
                            proof[Machine.Runnable_after_pop
                              m h_Runnable]› with
                      | .none => StepResult.done‹.error›
                      | .some ⟨pp, _⟩ =>
                          let mem' := placeStore
                            ‹mPopped↦mem, pp, retVal› ;
                          let mWithMem :=
                            mPopped[mem => mem'] ;
                          StepResult.ok‹jumpToBlock
                            ‹mWithMem, nextBlock,
                              proof[Machine.Runnable_after_mem_update
                                mPopped (Machine.Runnable_after_pop
                                  m h_Runnable) mem']››
                      end
                  | _ => StepResult.done‹.error›
                  end
              end
          end
      end

end Machine
