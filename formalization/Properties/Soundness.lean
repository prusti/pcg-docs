import Core.Doc.Interp
import Properties.Definitions

-- See `Properties.Definitions` for the rationale on `open
-- Machine`: it lets the property body's `Runnable`,
-- `initialMachine`, `step` references render unqualified.
open Machine

/-! # Soundness statement

The top-level guarantee that the PCG analysis is sound: under
the joined `validProgram` / `pcgAnalysisSucceeds` / `Reachable`
/ `Runnable` antecedents, `step` never produces an `error`
result. -/

defProperty Soundness (.plain "Soundness")
  short
    (.plain "the PCG analysis is sound")
  long
    (doc! "If the PCG analysis succeeds for a valid \
           program, every machine state reachable from \
           its #initialMachine is non-stuck — \
           #step never produces an error result.")
  := ∀∀ m ∈ Machine .
       -- The DSL lowers a top-level `A₁ ∧ … ∧ Aₙ → G`
       -- antecedent to a chain of named `(hᵢ : Aᵢ)` Pi
       -- binders (see `DslExpr.bindAntecedentNames`), so
       -- each conjunct's proof is in scope downstream by
       -- the auto-derived name `h_<head>`.
       ‹break› Runnable ‹m› ∧
       ‹break› pcgAnalysisSucceeds ‹prog ‹m›› ∧
       -- `Runnable` already implies `validProgram (prog m)`
       -- (its second conjunct), so we project it as
       -- `h_Runnable.2.1` to discharge `initialMachine`'s
       -- precondition rather than asserting `validProgram`
       -- as a separate antecedent.
       ‹break› Reachable
         ‹initialMachine
            ‹prog ‹m›, lean_proof("h_Runnable.2.1")›, m›
       -- `h_Runnable` is also in scope for `step`'s
       -- precondition on the goal side.
       → ‹break› step ‹m, lean_proof("h_Runnable")›
           ≠ StepResult.done‹.error›
