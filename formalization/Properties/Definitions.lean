import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw
import OpSem.Step
import PCG.Analyze.Body
import PCG.Capability
import PCG.PcgData
import PCG.PlaceCapability
import PCG.Reachability

-- Bring the source-side namespace into scope so that
-- references to `Runnable`, `step`, and
-- `initialMachine` can be written without the `Machine.`
-- qualifier. The DSL AST records the unqualified text, so
-- the LaTeX rendering displays the bare name.
open Machine

-- The infallible list-indexing inside `entryStateAt`
-- (`pdds[…]!`) requires `Inhabited PcgDomainData`. The DSL
-- has no `instance` syntax, so we declare the helper and the
-- two `Inhabited` instances as `defRaw` blocks: the inner
-- declarations are real Lean (the IDE keeps full
-- highlighting / hover / gotoDef on them) and the export
-- pipeline picks the verbatim source up via the registry.
-- The `requires contains(ar, l)` precondition on
-- `entryStateAt` guarantees the indexed element is always in
-- bounds, so the default is never actually reached.
defRaw middle =>
/-- A concrete `PcgData Place` inhabitant used as the default
    for `Inhabited (PcgData Place)`. It's never reached at
    runtime — the `requires contains(ar, l)` precondition on
    `entryStateAt` rules out the out-of-bounds branch — but
    the default still has to be definable for `pdds[…]!` to
    elaborate. -/
private def defaultPcgData : PcgData Place :=
  ⟨⟨mapEmpty⟩, ⟨[]⟩, ⟨0⟩, none⟩

defRaw middle =>
instance : Inhabited (PcgData Place) :=
  ⟨defaultPcgData⟩

defRaw middle =>
instance : Inhabited PcgDomainData :=
  ⟨⟨defaultPcgData,
    ⟨defaultPcgData, defaultPcgData,
     defaultPcgData, defaultPcgData⟩⟩⟩

/-! # Soundness supporting definitions

Definitions used by the soundness statement and the aliasing
properties: machine reachability, the program-wide analysis
driver, the analysis-results-describe-program relation,
analysis-state lookup helpers, and the place-level
`hasCapability` / `hasAllocation` relations that the property
bodies project through. The property statements themselves live
in `Properties.Aliasing` and `Properties.Soundness`. -/

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

defFn insertAnalyzedBody (.plain "insertAnalyzedBody")
  (.plain "Fold step for `analyzeProgram`: analyse a single \
    body and insert the result into the accumulating \
    `ProgAnalysisResults`. Short-circuits to `None` when \
    `analyzeBody` fails on the body.")
  (acc "The accumulating per-body analysis results."
      : ProgAnalysisResults)
  (b "The body to analyse." : Body)
  : Option ProgAnalysisResults :=
    let ar ← analyzeBody ‹b› ;
    Some (mapInsert ‹acc, b, ar›)

defFn analyzeProgram (.plain "analyzeProgram")
  (.seq [.plain "Run ", .code "analyzeBody",
    .plain " on every function body in the program, \
    accumulating the per-body results into a ",
    .code "ProgAnalysisResults",
    .plain ". Returns ", .code "None",
    .plain " when ", .code "analyzeBody",
    .plain " fails on any body."])
  (program "The program to analyse." : Program)
  : Option ProgAnalysisResults :=
    let bodies := mapValues ‹program↦functions› ;
    bodies·foldlM insertAnalyzedBody mapEmpty‹›

end Program

defInductiveProperty describes
  "Program Analysis Results Describe a Program"
  (.seq [.plain "Connects a ", .code "ProgAnalysisResults",
    .plain " value to the program it analyses: ",
    .code "par", .plain " describes ", .code "p",
    .plain " when running ", .code "analyzeProgram",
    .plain " on ", .code "p", .plain " yields ",
    .code "Some par", .plain "."])
  (par "The program analysis results."
      : ProgAnalysisResults)
  (p "The program." : Program)
  displayed (#par, .text " describes ", #p)
where
  | analyzeOk {par : ProgAnalysisResults} {p : Program}
      from (Program.analyzeProgram ‹p› = Some par)
      ⊢ describes ‹par, p›

defProperty pcgAnalysisSucceeds
    (.plain "pcgAnalysisSucceeds")
  short
    (.seq [.plain "the PCG analysis succeeds for program ",
           program])
  long
    (.seq [.plain "the PCG analysis succeeds for program ",
           program, .plain ": ",
           .code "analyzeProgram",
           .plain " returns ", .code "Some"])
  (program "The program to analyse." : Program)
  :=
    match Program.analyzeProgram ‹program› with
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

defFn pcgEntryStateAt (.plain "pcgEntryStateAt")
  (doc! "The PCG state on entry to the statement at location \
    `l` of body `b` in program-wide analysis results `par`: \
    looks up the body's per-body analysis results, then \
    defers to #entryStateAt. The #programContains \
    precondition guarantees both lookups succeed.")
  (par "The program analysis results."
      : ProgAnalysisResults)
  (b "The function body." : Body)
  (l "The location to look up." : Location)
  requires programContains(par, b, l)
  : PcgData Place :=
    let ar := mapAt ‹par, b› ;
    entryStateAt ‹ar, l, lean_proof("h_programContains.2")›

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
    let ⟨pp, _⟩ ← evalPlace
      ‹m, p, lean_proof("h_Runnable")› ;
    let prov ← pp↦ptr↦provenance ;
    Some (m↦mem↦allocs ! prov↦id↦index)

end Machine

defInductiveProperty hasCapability
  "PCG Place Capability"
  (.seq [.plain "Holds when the PCG data ", .code "pcg",
    .plain " (interpreted in body ", .code "b", .plain ") \
    assigns capability ", .code "c", .plain " to place ",
    .code "p", .plain "."])
  (pcg "The PCG data." : PcgData Place)
  (b "The function body." : Body)
  (p "The place." : Place)
  (c "The capability." : Capability)
  -- Renders as `pcg[p, b] ≐ c`. The user-facing notation
  -- `pcg[p]_b ≐ c` would put `b` in a subscript, but the
  -- displayed-template machinery escapes `_` (and parameter
  -- references can't sit inside a single subscript braces
  -- group), so the body is rendered as a comma-separated
  -- index instead.
  displayed (#pcg, .raw "[", #p, .sym .comma, #b,
             .raw "] \\doteq ", #c)
where
  | fromGet {pcg : PcgData Place} {b : Body}
        {p : Place} {c : Capability}
        {h_validPlace : validPlace b p}
      from (getCapability ‹pcg, b, p, lean_proof("h_validPlace")›
              = Some c)
      ⊢ hasCapability ‹pcg, b, p, c›

defInductiveProperty hasAllocation
  "Machine Place Allocation"
  (.seq [.plain "Holds when the machine state ", .code "m",
    .plain " backs place ", .code "p",
    .plain " with allocation ", .code "a", .plain "."])
  (m "The machine state." : Machine)
  (p "The place." : Place)
  (a "The allocation." : Allocation)
  displayed (#m, .raw "[", #p, .raw "] \\doteq ", #a)
where
  | fromGet {m : Machine} {p : Place} {a : Allocation}
        {h_Runnable : Runnable m}
      from (Machine.placeAllocation
              ‹m, p, lean_proof("h_Runnable")›
              = Some a)
      ⊢ hasAllocation ‹m, p, a›
