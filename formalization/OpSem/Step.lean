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
        proof[(by
          -- `frame` is `currentFrame m _`, which unfolds to
          -- `m.thread.stack.head!`. `Runnable m` gives us
          -- `stack ≠ [] ∧ validProgram ∧ validStack`; the
          -- inductive `validStack` then exposes
          -- `validStackFrame m.mem f` for any `f ∈ stack`
          -- via `validStack.frame_valid`.
          show validStackFrame m.mem
                  (currentFrame m h_Runnable)
          unfold currentFrame
          match hcase : m.thread.stack, h_Runnable.1 with
          | [], hne => exact absurd rfl hne
          | hd :: tl, _ =>
            -- The match arm has substituted `m.thread.stack`
            -- with `hd :: tl` in the goal; thread the same
            -- substitution into `h_Runnable.2.2.2` via
            -- `hcase ▸` so its type matches the cons-shaped
            -- stack the frame_valid lookup expects.
            exact validStack.frame_valid
              (hcase ▸ h_Runnable.2.2.2)
              List.mem_cons_self)]
        proof[(by
          -- `h_pre1 : validStatement frame.body (.storageLive lcl)`
          -- (the second precondition, named positionally
          -- because its first argument isn't a bare variable
          -- the DSL can lower to a `.named` precondition).
          -- `validStatement` on `.storageLive` reduces to
          -- `validLocal body lcl` by definition.
          show validLocal frame.body lcl
          simpa [validStatement] using h_pre1)] ;
      let rest := stackTail
        m proof[h_Runnable] ;
      Some m[mem => mem'][thread => Thread⟨frame' :: rest⟩]
  | m ; .storageDead lcl =>
      let frame := currentFrame
        m proof[h_Runnable] ;
      let ⟨frame', mem'⟩ := StackFrame.storageDead
        frame m↦mem lcl
        proof[(by
          show validStackFrame m.mem
                  (currentFrame m h_Runnable)
          unfold currentFrame
          match hcase : m.thread.stack, h_Runnable.1 with
          | [], hne => exact absurd rfl hne
          | hd :: tl, _ =>
            -- The match arm has substituted `m.thread.stack`
            -- with `hd :: tl` in the goal; thread the same
            -- substitution into `h_Runnable.2.2.2` via
            -- `hcase ▸` so its type matches the cons-shaped
            -- stack the frame_valid lookup expects.
            exact validStack.frame_valid
              (hcase ▸ h_Runnable.2.2.2)
              List.mem_cons_self)]
        proof[(by
          -- Same caveat as `.storageLive` above.
          show validLocal frame.body lcl
          simpa [validStatement] using h_pre1)] ;
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
        proof[(by
          -- `frame` is `currentFrame m _`, which unfolds to
          -- `m.thread.stack.head!`. `Runnable m`'s third
          -- conjunct is `validStack stack mem`; for any
          -- `f ∈ stack`, `validStack.frame_valid` gives back
          -- `validStackFrame m.mem f`, and projecting `.2.1`
          -- yields `validLocation frame.body frame.pc`.
          show validLocation
            (currentFrame m h_Runnable).body
            (currentFrame m h_Runnable).pc
          unfold currentFrame
          match hcase : m.thread.stack, h_Runnable.1 with
          | [], hne => exact absurd rfl hne
          | hd :: tl, _ =>
            -- The match arm has substituted `m.thread.stack`
            -- with `hd :: tl` in the goal. Thread the same
            -- substitution into `h_Runnable.2.2.2`'s type via
            -- `hcase ▸` so `validStack.frame_valid` lines up
            -- with the cons-shaped stack.
            exact (validStack.frame_valid
              (hcase ▸ h_Runnable.2.2.2)
              List.mem_cons_self).2.1)] with
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
                    (currentFrame m h_Runnable) := by
                unfold currentFrame
                match hcase :
                    m.thread.stack, h_Runnable.1 with
                | [], hne => exact absurd rfl hne
                | hd :: tl, _ =>
                  exact validStack.frame_valid
                    (hcase ▸ h_Runnable.2.2.2)
                    List.mem_cons_self
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
