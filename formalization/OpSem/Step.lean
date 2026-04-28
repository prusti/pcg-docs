import Core.Dsl.DefEnum
import Core.Dsl.DefFn
import MIR.StmtOrTerminator
import OpSem.Machine

defEnum ExecutionResult (.raw "er", .doc (.plain "ExecutionResult"))
  "Execution Results"
  (.seq [.plain "An execution result ",
    Doc.defMath (.raw "er")
      (.doc (.plain "ExecutionResult")),
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

defEnum StepResult (.raw "sr", .doc (.plain "StepResult"))
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
    machine, returning the resulting machine state. Currently \
    a placeholder that always fails (",
    .code "None",
    .plain "); real evaluation has not yet been implemented."])
  (m "The machine state." : Machine)
  (s "The statement to evaluate." : Statement)
  : Option Machine :=
    None

defFn evalTerminator (.plain "evalTerminator")
  (.seq [.plain "Evaluate a basic block terminator. The \
    terminator is responsible for advancing the program \
    counter — including switching to a new basic block when \
    appropriate. Currently a placeholder that always halts \
    with ", .code "error", .plain "; real evaluation has \
    not yet been implemented."])
  (m "The machine state." : Machine)
  (t "The terminator to evaluate." : Terminator)
  : StepResult :=
    StepResult.done‹.error›

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
    | .terminator t => evalTerminator ‹m, t›
    | .stmt s =>
        match evalStatement ‹m, s› with
        | .none => StepResult.done‹.error›
        | .some m' =>
            match m'↦thread↦stackFrames with
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
