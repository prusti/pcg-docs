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
    (.plain "If the PCG analysis succeeds for a valid \
            program, every machine state reachable from \
            its \\texttt{initialMachine} is non-stuck — \
            \\texttt{step} never produces an error result.")
  := ∀∀ pr ∈ Program, m ∈ Machine .
       ‹break› validProgram ‹pr› ∧
       ‹break› pcgAnalysisSucceeds ‹pr› ∧
       ‹break› Reachable
         -- The DSL lowers a top-level `A₁ ∧ … ∧ Aₙ → G`
         -- antecedent to a chain of named `(hᵢ : Aᵢ)` Pi
         -- binders (see `DslExpr.bindAntecedentNames`), so
         -- each conjunct's proof is in scope downstream by
         -- the auto-derived name `h_<head>`. The first
         -- conjunct here, `validProgram pr`, gives the
         -- binder `h_validProgram`.
         ‹initialMachine
            ‹pr, lean_proof("h_validProgram")›, m› ∧
       ‹break› Runnable ‹m›
       -- And the fourth conjunct gives `h_Runnable`, in
       -- scope for `step`'s precondition on the goal side.
       → ‹break› step ‹m, lean_proof("h_Runnable")›
           ≠ StepResult.done‹.error›
