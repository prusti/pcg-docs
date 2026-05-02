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
-- The `requires contains ar l` precondition on
-- `entryStateAt` guarantees the indexed element is always in
-- bounds, so the default is never actually reached.
defRaw middle =>
/-- A concrete `PcgData Place` inhabitant used as the default
    for `Inhabited (PcgData Place)`. It's never reached at
    runtime — the `requires contains ar l` precondition on
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

defInductiveProperty Step
  "Single-Step Transitions"
  (doc! "Holds when `m'` is derivable from `m` by a single successful #step transition (one whose \
    result is `.ok`). #[Reachable] then takes the reflexive-transitive closure of this relation.")
  (m "The pre-step machine state." : Machine)
  (m' "The post-step machine state." : Machine)
  displayed doc! "$#m \\rightsquigarrow #m'$"
where
  | takeStep {m, m' : Machine} {h : Runnable m}
      from (step m h = StepResult.ok m')
      ⊢ Step m m'

defInductiveProperty Reachable
  "Reachable Machines"
  (doc! "Reflexive-transitive closure of #Step: `Reachable m m'` holds when `m'` is derivable \
    from `m` by zero or more successful `step` transitions.")
  (m "The starting machine state." : Machine)
  (m' "A machine state reachable from m." : Machine)
  displayed doc! "$#m \\rightsquigarrow^* #m'$"
where
  | refl {m : Machine}
      ⊢ Reachable m m
  | stepOk {m, m', m'' : Machine}
      from (Reachable m m'',
            Step m'' m')
      ⊢ Reachable m m'

namespace Program

defFn analyzeBodies (.plain "analyzeBodies")
  (doc! "Recursive helper for #[analyzeProgram]: walk a list of bodies (all of which the caller \
    must have established as valid via the precondition), analyse each one, and accumulate the \
    results keyed by the body itself. Returns `None` as soon as #analyzeBody fails on any body.")
  (acc "The accumulating per-body analysis results."
      : ProgAnalysisResults)
  (bodies "The bodies still to analyse." : List Body)
  requires bodies·forAll fun b => validBody b
  : Option ProgAnalysisResults where
  | acc ; [] => Some acc
  | acc ; b :: rest =>
      let ar ← analyzeBody
        b proof[h_pre0 b (List.mem_cons_self ..)] ;
      analyzeBodies (mapInsert acc b ar) rest

defFn analyzeProgram (.plain "analyzeProgram")
  (doc! "Run #analyzeBody on every function body in the program, accumulating the per-body results \
    into a #ProgAnalysisResults. Returns `None` when #analyzeBody fails on any body.")
  (program "The program to analyse." : Program)
  requires validProgram program
  : Option ProgAnalysisResults :=
    -- `validProgram` guarantees both clauses of `analyzeBodies`'s
    -- precondition: the second conjunct of `validProgram` is
    -- exactly `forAll b ∈ mapValues program.functions, validBody b`.
    analyzeBodies mapEmpty‹› (mapValues program↦functions) proof[h_validProgram.2]

end Program

defInductiveProperty describes
  "Program Analysis Results Describe a Program"
  (doc! "Connects a #ProgAnalysisResults value to the program it analyses: `par` describes `p` when \
    running `analyzeProgram` on `p` yields `Some par`.")
  (par "The program analysis results."
      : ProgAnalysisResults)
  (p "The program." : Program)
  displayed doc! "$#par$ describes $#p$"
where
  | analyzeOk {par : ProgAnalysisResults} {p : Program}
        {h_validProgram : validProgram p}
      from (Program.analyzeProgram
              p proof[h_validProgram] = Some par)
      ⊢ describes par p

defProperty pcgAnalysisSucceeds
    (.plain "pcgAnalysisSucceeds")
  short
    (doc! "the PCG analysis succeeds for program {program}")
  long
    (doc! "the PCG analysis succeeds for program {program}: \
      `analyzeProgram` returns `Some`")
  (program "The program to analyse." : Program)
  :=
    -- `analyzeProgram` requires `validProgram program`, but
    -- `defProperty` has no `requires` clause. Phrase the
    -- precondition as an implication antecedent instead: the
    -- DSL lowers a top-level `A → G` to a Pi binder named
    -- `h_<head>`, so `h_validProgram : validProgram program`
    -- is in scope on the goal side and discharges
    -- `analyzeProgram`'s precondition without a `sorry`.
    validProgram program
    → match Program.analyzeProgram
              program proof[h_validProgram] with
      | .some _ => true
      | .none => false
      end

defFn entryStateAt (.plain "entryStateAt")
  (doc! "The PCG state on entry to the statement at location `l` in analysis results `ar`: indexes \
    the per-block list at the location's statement index and returns the recorded entry state. The \
    #contains precondition guarantees both lookups succeed.")
  (ar "The analysis results." : AnalysisResults)
  (l "The location to look up." : Location)
  requires contains ar l
  : PcgData Place :=
    let pdds := mapAt ar l↦block ;
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
  requires programContains par b l
  : PcgData Place :=
    let ar := mapAt par b ;
    entryStateAt ar l proof[h_programContains.2]

namespace Machine

defFn placeAllocation (.plain "placeAllocation")
  (doc! "The allocation backing a MIR place in a machine state: evaluates the place to a runtime \
    address and returns the allocation referenced by the resulting pointer's provenance. `None` when \
    the place cannot be evaluated or the resulting pointer has no provenance.")
  (m "The machine state." : Machine)
  (p "The place." : Place)
  requires Runnable m
  : Option Allocation :=
    let ⟨pp, _⟩ ← evalPlace
      m p proof[h_Runnable] ;
    let prov ← pp↦ptr↦provenance ;
    Some (m↦mem↦allocs ! prov↦id↦index)

end Machine

defInductiveProperty hasCapability
  "PCG Place Capability"
  (doc! "Holds when the PCG data `pcg` (interpreted in body `b`) assigns capability `c` to place \
    `p`.")
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
  displayed doc! "$#pcg[#p, #b] ≐ #c$"
where
  | fromGet {pcg : PcgData Place} {b : Body}
        {p : Place} {c : Capability}
        {h_validPlace : validPlace b p}
      from (getCapability pcg b p proof[h_validPlace]
              = Some c)
      ⊢ hasCapability pcg b p c

defInductiveProperty hasAllocation
  "Machine Place Allocation"
  (doc! "Holds when the machine state `m` backs place `p` with allocation `a`.")
  (m "The machine state." : Machine)
  (p "The place." : Place)
  (a "The allocation." : Allocation)
  displayed doc! "$#m[#p] ≐ #a$"
where
  | fromGet {m : Machine} {p : Place} {a : Allocation}
        {h_Runnable : Runnable m}
      from (Machine.placeAllocation
              m p proof[h_Runnable]
              = Some a)
      ⊢ hasAllocation m p a
