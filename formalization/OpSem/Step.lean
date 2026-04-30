import Core.Dsl.DefFn
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import MIR.StmtOrTerminator
import OpSem.Expressions.Place
import OpSem.Machine
import OpSem.Statements
import OpSem.StepResult
import OpSem.Terminator

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
