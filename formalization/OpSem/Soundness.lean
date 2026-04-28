import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import OpSem.Step
import PCG.Analyze.Body
import PCG.PcgData

/-! # Soundness statement

This module is intentionally **not** part of the `OpSem` umbrella
(`OpSem.lean`). The `RustExport` driver imports `OpSem`, and pulling
PCG analysis machinery into that import chain shifts the registry
order in ways that mis-resolve unqualified `.deref` constructors
inside previously-working PCG modules — the same failure mode the
top-of-file comment in `RustExport.lean` calls out for `PCG.Obtain`.

Importing this file is therefore opt-in: `LeanExport` and
`PresentationExport` import it explicitly so the soundness
definitions appear in the generated Lean project and the LaTeX
presentation, while `RustExport` continues to see only the original
`OpSem` chain (these definitions are Prop-level and would be
filtered out of Rust output anyway). -/

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
           programDoc, .plain ": running ",
           .code "analyzeBody",
           .plain " on the start function's body returns ",
           .code "Some"])
  (program "The program to analyse." : Program)
  :=
    match mapGet ‹program↦functions, program↦start› with
    | .some body =>
        let init :=
          PcgData⟨BorrowsGraph⟨mapEmpty‹›⟩,
            OwnedState⟨[]⟩, BasicBlockIdx⟨0⟩, None⟩ ;
        analyzeBody ‹init, body›·isSome
    | .none => false
    end

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
