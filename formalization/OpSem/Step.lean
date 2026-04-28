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
    .plain " cases are not yet modelled (return ",
    .code "None", .plain ")."])
  (m "The machine state." : Machine)
  (s "The statement to evaluate." : Statement)
  requires RunnableMachine(m)
  : Option Machine where
  | m ; .assign destination source =>
      let ⟨place, _⟩ ← evalPlace
        ‹m, destination, lean_proof("h_RunnableMachine")› ;
      let val ← evalRvalue
        ‹m, source, lean_proof("h_RunnableMachine")› ;
      Some m[mem => placeStore ‹m↦mem, place, val›]
  | _ ; .storageLive _ => None
  | _ ; .storageDead _ => None

defFn jumpToBlock (.plain "jumpToBlock")
  (.seq [.plain "Set the current frame's program counter to \
    statement 0 of ", .code "target",
    .plain ", leaving the rest of the call stack and memory \
    unchanged. Mirrors MiniRust's ",
    .code "jump_to_block", .plain "."])
  (m "The machine state." : Machine)
  (target "The basic block to jump to." : BasicBlockIdx)
  requires RunnableMachine(m)
  : Machine :=
    let frame := currentFrame
      ‹m, lean_proof("h_RunnableMachine")› ;
    let rest :=
      match m↦thread↦stack with
      | _ :: r => r
      | [] => []
      end ;
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
    .code "switchInt", .plain " and ", .code "call",
    .plain " currently halt with ", .code "error",
    .plain " — switch case maps and function-pointer \
    resolution are not yet modelled."
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
  requires RunnableMachine(m)
  : StepResult where
  | m ; .goto target =>
      StepResult.ok‹jumpToBlock
        ‹m, target, lean_proof("h_RunnableMachine")››
  | _ ; .unreachable => StepResult.done‹.error›
  | m ; .drop _ target =>
      StepResult.ok‹jumpToBlock
        ‹m, target, lean_proof("h_RunnableMachine")››
  | _ ; .switchInt _ => StepResult.done‹.error›
  | _ ; .call _ _ _ _ => StepResult.done‹.error›
  | m ; .return_ =>
      let frame := currentFrame
        ‹m, lean_proof("h_RunnableMachine")› ;
      let retTy := frame↦body↦decls ! 0 ;
      match mapGet ‹frame↦locals, Local⟨0⟩› with
      | .none => StepResult.done‹.error›
      | .some retPtr =>
          match typedLoad ‹m↦mem, retPtr, retTy› with
          | .none => StepResult.done‹.error›
          | .some retVal =>
              match m↦thread↦stack with
              | [] => StepResult.done‹.error›
              | _ :: rest =>
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
    .code "RunnableMachine",
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
  requires RunnableMachine(m)
  : StepResult :=
    let frame := currentFrame
      ‹m, lean_proof("h_RunnableMachine")› ;
    match getStmtOrTerminator
        ‹frame↦body, frame↦pc, lean_proof("sorry")› with
    | .terminator t =>
        evalTerminator ‹m, t, lean_proof("h_RunnableMachine")›
    | .stmt s =>
        match evalStatement
            ‹m, s, lean_proof("h_RunnableMachine")› with
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

defInductiveProperty Reachable
    (.text "reach", .text "Reachable")
  "Reachable Machines"
  (.seq [.plain "The set of machine states reachable from a \
    starting state by zero or more successful ", .code "step",
    .plain " transitions. ", .code "Reachable init m",
    .plain " holds when ", .code "m", .plain " is derivable \
    from ", .code "init", .plain " by repeated invocations of ",
    .code "step", .plain " whose results are ", .code ".ok",
    .plain "."])
  (init "The starting machine state." : Machine)
  (m "A reachable machine state." : Machine)
where
  | refl {init : Machine}
      ⊢ Reachable ‹init, init›
  | stepOk {init, m, m' : Machine}
        {h : Machine.RunnableMachine m'}
      from (Reachable ‹init, m'›,
            Machine.step ‹m', h› = StepResult.ok ‹m›)
      ⊢ Reachable ‹init, m›

defProperty pcgAnalysisSucceeds
    (.plain "pcgAnalysisSucceeds")
  short (programDoc) =>
    (.seq [.plain "the PCG analysis succeeds for program ",
           programDoc])
  long (programDoc) =>
    (.seq [.plain "the PCG analysis succeeds for program ",
           programDoc])
  (program "The program to analyse." : Program)
  := 0 = 0

defProperty Soundness (.plain "Soundness")
  short () =>
    (.plain "the PCG analysis is sound")
  long () =>
    (.plain "If the PCG analysis succeeds for a valid \
            program, every machine state reachable from \
            its \\texttt{initialMachine} is non-stuck — \
            \\texttt{step} never produces an error result.")
  := ∀∀ program, ∀∀ m,
       validProgram ‹program› →
       pcgAnalysisSucceeds ‹program› →
       Reachable
         -- The `validProgram` hypothesis bound by the
         -- preceding implication is proof-irrelevant for
         -- `initialMachine`, so injecting `sorry` here
         -- gives the same `Machine` term as any concrete
         -- proof would.
         ‹Machine.initialMachine
            ‹program, lean_proof("sorry")›, m›
         →
       Machine.RunnableMachine ‹m› →
       -- Same proof-irrelevance argument as above for the
       -- `RunnableMachine` precondition of `step`.
       Machine.step ‹m, lean_proof("sorry")›
         ≠ StepResult.done‹.error›
