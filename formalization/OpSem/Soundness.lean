import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import OpSem.Step
import PCG.Analyze.Body
import PCG.Capability
import PCG.PcgData
import PCG.PlaceCapability

-- Bring the source-side namespace into scope so that
-- references to `Runnable`, `step`, and
-- `initialMachine` can be written without the `Machine.`
-- qualifier. The DSL AST records the unqualified text, so
-- the LaTeX rendering displays the bare name.
open Machine

-- Source-only `Inhabited PcgDomainData` so the infallible
-- list-indexing inside `entryStateAt` (`pdds[…]!`, expanded
-- by the DSL macro) elaborates against the source `defStruct`
-- chain — `DomainData`/`PcgData` are generic, so the export
-- doesn't auto-derive `Inhabited` for them. The
-- `requires contains(ar, l)` precondition guarantees the
-- index is always in bounds, so the default value is never
-- actually evaluated; we still provide a concrete inhabitant
-- so eager elaboration can't trip on `sorry`. The Lean exporter
-- mirrors this with an `extraLeanItems` entry so the generated
-- project type-checks too.
private def defaultPcgData : PcgData Place :=
  ⟨⟨mapEmpty⟩, ⟨[]⟩, ⟨0⟩, none⟩

private instance : Inhabited (PcgData Place) :=
  ⟨defaultPcgData⟩

private instance : Inhabited PcgDomainData :=
  ⟨⟨defaultPcgData,
    ⟨defaultPcgData, defaultPcgData,
     defaultPcgData, defaultPcgData⟩⟩⟩

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
  "Reachable Machines"
  (.seq [.plain "The set of machine states reachable from a \
    starting state by zero or more successful ", .code "step",
    .plain " transitions. ", .code "Reachable m m'",
    .plain " holds when ", .code "m'", .plain " is derivable \
    from ", .code "m", .plain " by repeated invocations of ",
    .code "step", .plain " whose results are ", .code ".ok",
    .plain "."])
  (m "The starting machine state." : Machine)
  (m' "A machine state reachable from m." : Machine)
  displayed (#m, .raw " \\rightsquigarrow^{*} ", #m')
where
  | refl {m : Machine}
      ⊢ Reachable ‹m, m›
  | stepOk {m, m', m'' : Machine}
        {h : Runnable m''}
      from (Reachable ‹m, m''›,
            step ‹m'', h› = StepResult.ok ‹m'›)
      ⊢ Reachable ‹m, m'›

namespace Program

defFn analyzeProgram (.plain "analyzeProgram")
  (.seq [.plain "Run ", .code "analyzeBody",
    .plain " on the start function's body, starting from a \
    fresh PCG with an empty borrows graph and the entry-point \
    owned state derived from the body via ",
    .code "OwnedState.initial",
    .plain ". The ", .code "validProgram",
    .plain " precondition makes the start-function lookup \
    total via ", .code "startProgram", .plain "; the result \
    is still ", .code "Option AnalysisResults",
    .plain " because ", .code "analyzeBody",
    .plain " can fail on a block."])
  (program "The program to analyse." : Program)
  requires validProgram(program)
  : Option AnalysisResults :=
    let body := startProgram
      ‹program, lean_proof("h_validProgram")› ;
    let init :=
      PcgData⟨BorrowsGraph⟨mapEmpty‹›⟩,
        OwnedState.initial ‹body›,
        BasicBlockIdx⟨0⟩, None⟩ ;
    analyzeBody ‹init, body›

end Program

defInductiveProperty describes
  "Analysis Results Describe a Program"
  (.seq [.plain "Connects an ", .code "AnalysisResults",
    .plain " value to the program it analyses: ",
    .code "ar", .plain " describes ", .code "p",
    .plain " when running ", .code "analyzeProgram",
    .plain " on ", .code "p", .plain " yields ",
    .code "Some ar", .plain "."])
  (ar "The analysis results." : AnalysisResults)
  (p "The program." : Program)
  displayed (#ar, .text " describes ", #p)
where
  | analyzeOk {ar : AnalysisResults} {p : Program}
      from (Program.analyzeProgram ‹p, lean_proof("sorry")›
              = Some ar)
      ⊢ describes ‹ar, p›

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
    match Program.analyzeProgram
            ‹program, lean_proof("sorry")› with
    | .some _ => true
    | .none => false
    end

defFn entryStateAt (.plain "entryStateAt")
  (.seq [.plain "The PCG state on entry to the statement at \
    location ", .code "l", .plain " in analysis results ",
    .code "ar", .plain ": indexes the per-block list at the \
    location's statement index and returns the recorded \
    entry state. The ", .code "contains",
    .plain " precondition guarantees both lookups succeed."])
  (ar "The analysis results." : AnalysisResults)
  (l "The location to look up." : Location)
  requires contains(ar, l)
  : PcgData Place :=
    let pdds := mapAt ‹ar, l↦block› ;
    let pdd := pdds ! l↦stmtIdx ;
    pdd↦entryState

namespace Machine

defFn placeAllocation (.plain "placeAllocation")
  (.seq [.plain "The allocation backing a MIR place in a \
    machine state: evaluates the place to a runtime address \
    and returns the allocation referenced by the resulting \
    pointer's provenance. ", .code "None",
    .plain " when the place cannot be evaluated or the \
    resulting pointer has no provenance."])
  (m "The machine state." : Machine)
  (p "The place." : Place)
  requires Runnable(m)
  : Option Allocation :=
    let ⟨rp, _⟩ ← evalPlace
      ‹m, p, lean_proof("h_Runnable")› ;
    let prov ← rp↦ptr↦provenance ;
    Some (m↦mem↦allocs ! prov↦id↦index)

end Machine

defProperty Framing (.plain "Framing")
  short () =>
    (.plain "the PCG analysis frames non-aliasing of \
            exclusive places")
  long () =>
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state, two \
            places that the entry-state PCG at the machine's \
            program counter assigns the exclusive capability \
            are backed by distinct allocations.")
  := ∀∀ pr ∈ Program, ∀∀ ar ∈ AnalysisResults,
       describes ‹ar, pr› →
       ∀∀ m ∈ Machine,
         Reachable
           ‹initialMachine
              ‹pr, lean_proof("sorry")›, m› →
         Runnable ‹m› →
         ∀∀ p ∈ Place, ∀∀ p' ∈ Place,
           let frame := currentFrame
             ‹m, lean_proof("sorry")› ;
           validPlace ‹frame↦body, p› →
           validPlace ‹frame↦body, p'› →
           contains ‹ar, frame↦pc› →
           let pcg := entryStateAt
             ‹ar, frame↦pc, lean_proof("sorry")› ;
           (getCapability ‹pcg, frame↦body, p,
                           lean_proof("sorry")›
              = Some .exclusive) →
           (getCapability ‹pcg, frame↦body, p',
                           lean_proof("sorry")›
              = Some .exclusive) →
           Machine.placeAllocation
               ‹m, p, lean_proof("sorry")›
             ≠ Machine.placeAllocation
                 ‹m, p', lean_proof("sorry")›

defProperty Soundness (.plain "Soundness")
  short () =>
    (.plain "the PCG analysis is sound")
  long () =>
    (.plain "If the PCG analysis succeeds for a valid \
            program, every machine state reachable from \
            its \\texttt{initialMachine} is non-stuck — \
            \\texttt{step} never produces an error result.")
  := ∀∀ pr ∈ Program, ∀∀ m ∈ Machine,
       validProgram ‹pr› →
       pcgAnalysisSucceeds ‹pr› →
       Reachable
         -- The `validProgram` hypothesis bound by the
         -- preceding implication is proof-irrelevant for
         -- `initialMachine`, so injecting `sorry` here
         -- gives the same `Machine` term as any concrete
         -- proof would.
         ‹initialMachine
            ‹pr, lean_proof("sorry")›, m›
         →
       Runnable ‹m› →
       -- Same proof-irrelevance argument as above for the
       -- `Runnable` precondition of `step`.
       step ‹m, lean_proof("sorry")›
         ≠ StepResult.done‹.error›
