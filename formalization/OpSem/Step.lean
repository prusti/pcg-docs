import Core.Dsl.DefEnum
import Core.Dsl.DefFn
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import MIR.StmtOrTerminator
import OpSem.Expressions.Place
import OpSem.Machine
import OpSem.Statements

defEnum ExecutionResult (.raw "er", .text "ExecutionResult")
  "Execution Results"
  (.seq [.plain "An execution result ",
    Doc.defMath (.raw "er")
      (.text "ExecutionResult"),
    .plain " summarises the terminal status of a program: \
      either it ran to completion (",
    .code "success", .plain ") or it stopped abnormally (",
    .code "error", .plain ")."])
where
  | success
    "The program ran to completion."
  | error
    "The program halted abnormally."
  deriving Repr, BEq, Hashable

defEnum StepResult (.raw "sr", .text "StepResult")
  "Step Results"
  (.seq [.plain "The outcome of a single execution step. ",
    .code "done", .plain " indicates that the program has \
      finished, carrying an ", .code "ExecutionResult",
    .plain " describing how it ended; ", .code "ok",
    .plain " indicates that the step produced a new machine \
      state and execution should continue."])
  long where
  | done (result : ExecutionResult)
    "The program has finished with the given result."
  | ok (machine : Machine)
    "The step produced a new machine state."
  deriving Repr

defFn caseTarget (.plain "caseTarget")
  (.seq [.plain "Look up the basic block that a ",
    .code "switchInt", .plain " terminator should jump to \
    when its operand evaluates to ", .code "iv",
    .plain ". Scans the ", .code "cases",
    .plain " list in order for the first pair whose first \
    component is ", .code "iv",
    .plain "; returns the supplied ", .code "fallback",
    .plain " when no case matches. Mirrors MiniRust's ",
    .code "cases.get(value).unwrap_or(fallback)", .plain "."])
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

defFn evalStatement (.plain "evalStatement")
  (.seq [.plain "Evaluate a single MIR statement against the \
    machine, returning the resulting machine state. Mirrors \
    MiniRust's ", .code "Machine::eval_statement",
    .plain ". The ", .code "assign",
    .plain " case resolves the destination place via ",
    .code "evalPlace", .plain ", evaluates the rvalue via ",
    .code "evalRvalue", .plain ", and writes the value to \
    memory via ", .code "placeStore", .plain ". The ",
    .code "storageLive", .plain " and ", .code "storageDead",
    .plain " cases delegate to ",
    .code "StackFrame.storageLive", .plain " and ",
    .code "StackFrame.storageDead",
    .plain " on the current frame and reinstall the updated \
    frame and memory on the machine."])
  (m "The machine state." : Machine)
  (s "The statement to evaluate." : Statement)
  requires Runnable(m)
  : Option Machine where
  | m ; .assign destination source =>
      let ⟨place, _⟩ ← evalPlace
        ‹m, destination, lean_proof("h_Runnable")› ;
      let val ← evalRvalue
        ‹m, source, lean_proof("h_Runnable")› ;
      Some m[mem => placeStore ‹m↦mem, place, val›]
  | m ; .storageLive lcl =>
      let frame := currentFrame
        ‹m, lean_proof("h_Runnable")› ;
      let ⟨frame', mem'⟩ := StackFrame.storageLive
        ‹frame, m↦mem, lcl› ;
      let rest := stackTail
        ‹m, lean_proof("h_Runnable")› ;
      Some m[mem => mem'][thread => Thread⟨frame' :: rest⟩]
  | m ; .storageDead lcl =>
      let frame := currentFrame
        ‹m, lean_proof("h_Runnable")› ;
      let ⟨frame', mem'⟩ := StackFrame.storageDead
        ‹frame, m↦mem, lcl› ;
      let rest := stackTail
        ‹m, lean_proof("h_Runnable")› ;
      Some m[mem => mem'][thread => Thread⟨frame' :: rest⟩]

defFn jumpToBlock (.plain "jumpToBlock")
  (.seq [.plain "Set the current frame's program counter to \
    statement 0 of ", .code "target",
    .plain ", leaving the rest of the call stack and memory \
    unchanged. Mirrors MiniRust's ",
    .code "jump_to_block", .plain "."])
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
  (.seq [.plain "Evaluate a basic block terminator. The \
    terminator is responsible for advancing the program \
    counter — including switching to a new basic block when \
    appropriate."
    , .plain " ", .code "goto", .plain " jumps to its target \
    block via ", .code "jumpToBlock", .plain "; ",
    .code "drop", .plain " jumps to its successor without \
    modelling drop semantics; ", .code "unreachable",
    .plain " halts with ", .code "error", .plain "; ",
    .code "switchInt", .plain " evaluates its operand and \
    jumps to the case-matching basic block, falling back to \
    the terminator's ", .code "fallback",
    .plain " when no case matches (mirrors MiniRust's ",
    .code "Terminator::Switch", .plain "); ", .code "call",
    .plain " currently halts with ", .code "error",
    .plain " — function-pointer resolution is not yet \
    modelled."
    , .plain " ", .code "return", .plain " loads the return \
    value out of the callee's return slot (local 0), pops \
    the callee frame, and — when the call stack still \
    contains a caller — looks at the caller's pending call \
    terminator to recover the destination place and \
    successor block, stores the return value into the \
    destination, and jumps the caller to that block. When \
    the popped frame was the bottom of the stack, the \
    program halts with ", .code "success", .plain "."])
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
  | _ ; .call _ _ _ _ => StepResult.done‹.error›
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
                      | .some ⟨rp, _⟩ =>
                          let mem' := placeStore
                            ‹mPopped↦mem, rp, retVal› ;
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

defFn step (.plain "step")
  (.seq [.plain "Execute a single step of the operational \
    semantics. Looks up the program element at the current \
    frame's program counter via ",
    .code "getStmtOrTerminator", .plain ": a statement is \
    handed to ", .code "evalStatement",
    .plain " (and the resulting frame's ", .code "pc.stmtIdx",
    .plain " is advanced by one), a terminator is handed to ",
    .code "evalTerminator", .plain " which produces the next ",
    .code "StepResult", .plain " directly. The ",
    .code "Runnable",
    .plain " precondition guarantees a non-empty call stack \
    (so ", .code "currentFrame", .plain " returns directly) \
    and that every stack frame is valid (so the program \
    counter is a ", .code "validLocation",
    .plain " and ", .code "getStmtOrTerminator",
    .plain " applies). Mirrors MiniRust's ",
    .code "Machine::step",
    .plain ", minus thread scheduling, deadlock detection, \
    and data-race tracking — this model has only one thread."])
  (m "The machine state." : Machine)
  requires Runnable(m)
  : StepResult :=
    let frame := currentFrame
      ‹m, lean_proof("h_Runnable")› ;
    match getStmtOrTerminator
        ‹frame↦body, frame↦pc, lean_proof("sorry")› with
    | .terminator t =>
        evalTerminator ‹m, t, lean_proof("h_Runnable")›
    | .stmt s =>
        match evalStatement
            ‹m, s, lean_proof("h_Runnable")› with
        | .none => StepResult.done‹.error›
        | .some m' =>
            match m'↦thread↦stack with
            | [] => StepResult.done‹.error›
            | frame' :: rest =>
                let newPc :=
                  Location⟨frame'↦pc↦block,
                    frame'↦pc↦stmtIdx + 1⟩ ;
                StepResult.ok‹m'[thread =>
                  Thread⟨frame'[pc => newPc]
                    :: rest⟩]›
            end
        end
    end

end Machine
