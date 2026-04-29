import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import OpSem.Step
import PCG.Analyze.Body
import PCG.PcgData

-- Bring the source-side namespace into scope so that
-- references to `RunnableMachine`, `step`, and
-- `initialMachine` can be written without the `Machine.`
-- qualifier. The DSL AST records the unqualified text, so
-- the LaTeX rendering displays the bare name.
open Machine

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
        {h : RunnableMachine m'}
      from (Reachable ‹init, m'›,
            step ‹m', h› = StepResult.ok ‹m›)
      ⊢ Reachable ‹init, m›

namespace Program

defFn analyzeProgram (.plain "analyzeProgram")
  (.seq [.plain "Run ", .code "analyzeBody",
    .plain " on the start function's body, starting from a \
    fresh PCG with an empty borrows graph and the entry-point \
    owned state derived from the body via ",
    .code "initialState",
    .plain ". Returns ", .code "None",
    .plain " when the start function is unregistered or when ",
    .code "analyzeBody", .plain " fails on any block."])
  (program "The program to analyse." : Program)
  : Option AnalysisResults :=
    match mapGet ‹program↦functions, program↦start› with
    | .some body =>
        let init :=
          PcgData⟨BorrowsGraph⟨mapEmpty‹›⟩,
            Body.initialState ‹body›,
            BasicBlockIdx⟨0⟩, None⟩ ;
        analyzeBody ‹init, body›
    | .none => None
    end

end Program

defInductiveProperty describes
    (.text "d", .text "Describes")
  "Analysis Results Describe a Program"
  (.seq [.plain "Connects an ", .code "AnalysisResults",
    .plain " value to the program it analyses: ",
    .code "as", .plain " describes ", .code "p",
    .plain " when running ", .code "analyzeProgram",
    .plain " on ", .code "p", .plain " yields ",
    .code "Some as", .plain "."])
  (as "The analysis results." : AnalysisResults)
  (p "The program." : Program)
where
  | analyzeOk {as : AnalysisResults} {p : Program}
      from (Program.analyzeProgram ‹p› = Some as)
      ⊢ describes ‹as, p›

defProperty pcgAnalysisSucceeds
    (.plain "pcgAnalysisSucceeds")
  short (programDoc) =>
    (.seq [.plain "the PCG analysis succeeds for program ",
           programDoc])
  long (programDoc) =>
    (.seq [.plain "the PCG analysis succeeds for program ",
           programDoc, .plain ": ",
           .code "analyzeProgram",
           .plain " returns ", .code "Some"])
  (program "The program to analyse." : Program)
  :=
    match Program.analyzeProgram ‹program› with
    | .some _ => true
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
         ‹initialMachine
            ‹program, lean_proof("sorry")›, m›
         →
       RunnableMachine ‹m› →
       -- Same proof-irrelevance argument as above for the
       -- `RunnableMachine` precondition of `step`.
       step ‹m, lean_proof("sorry")›
         ≠ StepResult.done‹.error›
