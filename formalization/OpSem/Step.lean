import Core.Dsl.DefFn
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import MIR.StmtOrTerminator
import OpSem.Expressions.Place
import OpSem.Machine
import OpSem.Statements
import OpSem.StepResult
import OpSem.Terminator

-- Open `StackFrame` so the in-tree elaboration of the
-- proofs below resolves `validStackFrame` to
-- `StackFrame.validStackFrame`. The Lean exporter places
-- `validStackFrame` in `namespace Memory` (its first param's
-- type is `Memory`), which is already opened in the
-- generated file, so the same unqualified name works there.
open StackFrame

namespace Machine

-- The currently executing stack frame is itself a
-- `validStackFrame` against the machine's memory. Follows
-- from the inductive `validStack` clause of `Runnable m`:
-- the head of a non-empty `validStack` is a `validStackFrame`
-- via `validStack.frame_valid`. Used by the storage helpers
-- below and by `step` to discharge the `validStackFrame`
-- precondition of `StackFrame.storageLive` /
-- `StackFrame.storageDead` / `getStmtOrTerminator` at the
-- current frame.
defRaw middle =>
theorem Machine.currentFrame_validStackFrame
    (m : Machine) (h_Runnable : Machine.Runnable m) :
    validStackFrame m.mem (Machine.currentFrame m h_Runnable) := by
  unfold Machine.currentFrame
  match hcase : m.thread.stack, h_Runnable.1 with
  | [], hne => exact absurd rfl hne
  | hd :: tl, _ =>
    exact validStack.frame_valid
      (hcase ▸ h_Runnable.2.2.2)
      List.mem_cons_self

defFn evalStatement (.plain "evalStatement")
  (doc! "Evaluate a single MIR statement against the machine, returning the resulting machine \
    state. Mirrors MiniRust's `Machine::eval_statement`. The `assign` case resolves the destination \
    place via `evalPlace`, evaluates the rvalue via `evalRvalue`, and writes the value to memory via \
    `placeStore`. The `storageLive` and `storageDead` cases delegate to `StackFrame.storageLive` and \
    `StackFrame.storageDead` on the current frame and reinstall the updated frame and memory on the \
    machine. The #validStatement precondition discharges the #validLocal obligation those storage \
    helpers carry: when {s} is `.storageLive lcl` or `.storageDead lcl`, the precondition unfolds to \
    #validLocal on `frame.body` and `lcl` directly.")
  (m "The machine state." : Machine)
  (s "The statement to evaluate." : Statement)
  requires Runnable m,
    validStatement (currentFrame m h_Runnable)↦body s
  : Option Machine where
  | m ; .assign destination source =>
      let ⟨place, _⟩ ← evalPlace
        m destination proof[h_Runnable] ;
      let val ← evalRvalue
        m source proof[h_Runnable] ;
      Some m[mem => placeStore m↦mem place val]
  | m ; .storageLive lcl =>
      let frame := currentFrame
        m proof[h_Runnable] ;
      let ⟨frame', mem'⟩ := StackFrame.storageLive
        frame m↦mem lcl
        proof[Machine.currentFrame_validStackFrame m h_Runnable]
        -- `h_pre1 : validStatement frame.body (.storageLive lcl)`
        -- (named positionally because the precondition's first
        -- argument isn't a bare variable the DSL can lower to a
        -- `.named` form). `validStatement` on `.storageLive`
        -- reduces to `validLocal body lcl` by definition.
        proof[(by simpa [validStatement] using h_pre1)] ;
      let rest := stackTail
        m proof[h_Runnable] ;
      Some m[mem => mem'][thread => Thread⟨frame' :: rest⟩]
  | m ; .storageDead lcl =>
      let frame := currentFrame
        m proof[h_Runnable] ;
      let ⟨frame', mem'⟩ := StackFrame.storageDead
        frame m↦mem lcl
        proof[Machine.currentFrame_validStackFrame m h_Runnable]
        -- Same shape as the `.storageLive` arm above:
        -- `h_pre1 : validStatement frame.body (.storageDead lcl)`
        -- reduces to `validLocal frame.body lcl`.
        proof[(by simpa [validStatement] using h_pre1)] ;
      let rest := stackTail
        m proof[h_Runnable] ;
      Some m[mem => mem'][thread => Thread⟨frame' :: rest⟩]

defFn step (.plain "step")
  (doc! "Execute a single step of the operational semantics. Looks up the program element at the \
    current frame's program counter via #getStmtOrTerminator: a statement is handed to \
    `evalStatement` (and the resulting frame's `pc.stmtIdx` is advanced by one), a terminator is \
    handed to `evalTerminator` which produces the next #StepResult directly. The `Runnable` \
    precondition guarantees a non-empty call stack (so `currentFrame` returns directly) and that \
    every stack frame is valid (so the program counter is a #validLocation and #getStmtOrTerminator \
    applies). Mirrors MiniRust's `Machine::step`, minus thread scheduling, deadlock detection, and \
    data-race tracking — this model has only one thread.")
  (m "The machine state." : Machine)
  requires Runnable m
  : StepResult :=
    let frame := currentFrame
      m proof[h_Runnable] ;
    match heq : getStmtOrTerminator
        frame↦body frame↦pc
        proof[(Machine.currentFrame_validStackFrame
          m h_Runnable).2.1] with
    | .terminator t =>
        evalTerminator m t proof[h_Runnable]
    | .stmt s =>
        match evalStatement
            m s proof[h_Runnable]
            proof[(by
              -- The `.stmt s` case of `getStmtOrTerminator`
              -- — captured by `heq` — combined with the
              -- #validBody we can extract from `Runnable m`'s
              -- inductive `validStack` invariant, discharges
              -- the #validStatement obligation via
              -- `validStatement_of_getStmtOrTerminator_eq`.
              have h_vsf :
                  validStackFrame m.mem
                    (currentFrame m h_Runnable) :=
                Machine.currentFrame_validStackFrame
                  m h_Runnable
              exact validStatement_of_getStmtOrTerminator_eq
                _ _ h_vsf.1 h_vsf.2.1 heq)] with
        | .none => StepResult.done .error
        | .some m' =>
            match m'↦thread↦stack with
            | [] => StepResult.done .error
            | frame' :: rest =>
                let newPc :=
                  Location⟨frame'↦pc↦block,
                    frame'↦pc↦stmtIdx + 1⟩ ;
                StepResult.ok (m'[thread =>
                  Thread⟨frame'[pc => newPc]
                    :: rest⟩])
            end
        end
    end

end Machine
