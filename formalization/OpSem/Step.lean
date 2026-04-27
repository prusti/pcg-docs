import Core.Dsl.DefFn
import OpSem.Machine

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
    appropriate. Currently a placeholder that always fails (",
    .code "None",
    .plain "); real evaluation has not yet been implemented."])
  (m "The machine state." : Machine)
  (t "The terminator to evaluate." : Terminator)
  : Option Machine :=
    None

defFn step (.plain "step")
  (.seq [.plain "Execute a single step of the operational \
    semantics. Looks up the current basic block from the \
    executing stack frame's program counter; if the program \
    counter has advanced past the last statement, evaluates \
    the block's terminator (which itself updates the program \
    counter); otherwise evaluates the statement at ",
    .code "pc.stmtIdx",
    .plain " and advances the statement index by one. \
    Mirrors MiniRust's ", .code "Machine::step",
    .plain ", minus thread scheduling, deadlock detection, \
    and data-race tracking — this model has only one thread."])
  (m "The machine state." : Machine)
  : Option Machine :=
    let frame ← currentFrame ‹m› ;
    let block ←
      frame↦body↦basicBlocks !! frame↦pc↦block↦index ;
    if frame↦pc↦stmtIdx == block↦statements·length then
      evalTerminator ‹m, block↦terminator›
    else
      let stmt ← block↦statements !! frame↦pc↦stmtIdx ;
      let m' ← evalStatement ‹m, stmt› ;
      match m'↦thread↦stackFrames with
      | [] => None
      | frame' :: rest =>
          let newPc :=
            Location⟨frame'↦pc↦block,
              frame'↦pc↦stmtIdx + 1⟩ ;
          Some m'[thread =>
            Thread⟨frame'[pc => newPc] :: rest⟩]
      end

end Machine
