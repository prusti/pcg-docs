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
        ‹m, a, lean_proof("h_Runnable")› ;
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
      ‹m, lean_proof("h_Runnable")› ;
    let rest := stackTail
      ‹m, lean_proof("h_Runnable")› ;
    let newPc := Location⟨target, 0⟩ ;
    let newFrame := frame[pc => newPc] ;
    m[thread => Thread⟨newFrame :: rest⟩]

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
        ‹m, target, lean_proof("h_Runnable")››
  | _ ; .unreachable => StepResult.done‹.error›
  | m ; .drop _ target =>
      StepResult.ok‹jumpToBlock
        ‹m, target, lean_proof("h_Runnable")››
  | m ; .switchInt op cases fallback =>
      match evalOperand
          ‹m, op, lean_proof("h_Runnable")› with
      | .some (.int iv) =>
          let target := caseTarget ‹cases, iv, fallback› ;
          StepResult.ok‹jumpToBlock
            ‹m, target, lean_proof("h_Runnable")››
      | _ => StepResult.done‹.error›
      end
  | m ; .call calleeOp args _ _ =>
      match evalOperand
          ‹m, calleeOp, lean_proof("h_Runnable")› with
      | .none => StepResult.done‹.error›
      | .some calleeVal =>
          match fnFromPtr ‹m, calleeVal› with
          | .none => StepResult.done‹.error›
          | .some calleeBody =>
              match evalArgs
                  ‹m, args, lean_proof("h_Runnable")› with
              | .none => StepResult.done‹.error›
              | .some argVals =>
                  StepResult.ok‹createFrame
                    ‹m, calleeBody, argVals››
              end
          end
      end
  | m ; .return_ =>
      let frame := currentFrame
        ‹m, lean_proof("h_Runnable")› ;
      let retTy := frame↦body↦decls ! 0 ;
      match mapGet ‹frame↦locals, Local⟨0⟩› with
      | .none => StepResult.done‹.error›
      | .some retPtr =>
          match typedLoad ‹m↦mem, retPtr, retTy› with
          | .none => StepResult.done‹.error›
          | .some retVal =>
              let rest := stackTail
                ‹m, lean_proof("h_Runnable")› ;
              match rest with
              | [] => StepResult.done‹.success›
              | callerFrame :: _ =>
                  match getStmtOrTerminator
                      ‹callerFrame↦body, callerFrame↦pc,
                        lean_proof("sorry")› with
                  | .terminator (.call _ _ targetPlace
                      nextBlock) =>
                      let mPopped :=
                        m[thread => Thread⟨rest⟩] ;
                      match evalPlace
                          ‹mPopped, targetPlace,
                            lean_proof("sorry")› with
                      | .none => StepResult.done‹.error›
                      | .some ⟨pp, _⟩ =>
                          let mem' := placeStore
                            ‹mPopped↦mem, pp, retVal› ;
                          let mWithMem :=
                            mPopped[mem => mem'] ;
                          StepResult.ok‹jumpToBlock
                            ‹mWithMem, nextBlock,
                              lean_proof("sorry")››
                      end
                  | _ => StepResult.done‹.error›
                  end
              end
          end
      end

end Machine
