import Properties.Definitions

-- See `Properties.Definitions` for the rationale on `open
-- Machine`: it lets unqualified `Runnable`, `currBody`,
-- `currPC`, `initialMachine`, … flow through to the LaTeX
-- rendering as bare names.
open Machine

/-! # Aliasing properties

Properties that bound how the PCG analysis controls aliasing of
runtime allocations. `Framing` forbids two simultaneously-
exclusive places from sharing an allocation; `NoAlias`
strengthens the conclusion to non-overlapping address ranges,
under the weaker hypothesis that the two places' PCG nodes are
disconnected. -/

defProperty Framing (.plain "Framing")
  short () =>
    (.plain "the PCG analysis frames non-aliasing of \
            exclusive places")
  long () =>
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state, two \
            places that the entry-state PCG at the machine's \
            program counter assigns the exclusive capability \
            are backed by allocations whose address ranges \
            do not overlap.")
  := ∀∀ pr ∈ Program, par ∈ ProgAnalysisResults,
        m ∈ Machine,
        p p' ∈ Place, a a' ∈ Allocation .
       ‹break› describes ‹par, pr› →
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("sorry")›, m› →
       ‹break› Runnable ‹m› →
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p› →
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p'› →
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("sorry")›,
          currPC ‹m, lean_proof("sorry")›› →
       ‹break› hasCapability
         ‹programEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          currBody ‹m, lean_proof("sorry")›,
          p, .exclusive› →
       ‹break› hasCapability
         ‹programEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          currBody ‹m, lean_proof("sorry")›,
          p', .exclusive› →
       ‹break› hasAllocation ‹m, p, a› →
       ‹break› hasAllocation ‹m, p', a'› →
       ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty NoAlias (.plain "NoAlias")
  short () =>
    (.plain "the PCG analysis frames non-overlap of \
            disconnected places")
  long () =>
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state, two \
            places whose corresponding PCG nodes are not \
            connected in the entry-state PCG at the machine's \
            program counter are backed by allocations whose \
            address ranges do not overlap. The conclusion is \
            phrased as a disjunction `connected ∨ \
            nonOverlapping` so that the property's contrapositive \
            reads as the disconnected-implies-disjoint statement \
            without needing a negation operator in the DSL.")
  := ∀∀ pr ∈ Program, par ∈ ProgAnalysisResults,
        m ∈ Machine,
        p p' ∈ Place, a1 a2 ∈ Allocation .
       ‹break› describes ‹par, pr› →
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("sorry")›, m› →
       ‹break› Runnable ‹m› →
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p› →
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p'› →
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("sorry")›,
          currPC ‹m, lean_proof("sorry")›› →
       ‹break› (Machine.placeAllocation
            ‹m, p, lean_proof("sorry")›
          = Some a1) →
       ‹break› (Machine.placeAllocation
            ‹m, p', lean_proof("sorry")›
          = Some a2) →
       ‹break› connected
         ‹programEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          placeNode ‹p›, placeNode ‹p'›› ∨
       ‹break› Allocation.nonOverlapping ‹a1, a2›
