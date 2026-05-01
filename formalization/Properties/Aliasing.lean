import Core.Doc.Interp
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
disconnected.

`Framing` factors its core relationship between a machine and a
PCG out into `FramingInvariant`, a stand-alone property over
`(m, pcg)` that asserts non-overlap of allocations for any pair
of exclusively-capability-tagged places. The unprimed `Framing`
then merely sets up the program-level antecedents (analysis
describes program, reachability, runnability, program-contains)
that ground the `pcgEntryStateAt` lookup, and applies
`FramingInvariant`.

`NoAlias` mirrors `Framing`'s split: `NoAliasInvariant` is a
stand-alone property over `(m, pcg)` that asserts the
disconnected-implies-disjoint conclusion for any pair of valid
places, and the unprimed `NoAlias` sets up the program-level
antecedents (analysis describes program, reachability,
runnability, program-contains) that ground the
`pcgEntryStateAt` lookup, and applies `NoAliasInvariant`. -/

defProperty FramingInvariant (.plain "FramingInvariant")
  short
    (doc! "the framing invariant holds between {m} and {pcg}")
  long
    (doc! "Holds when, for every pair of distinct places \
           assigned the exclusive capability by {pcg} \
           (interpreted in {m}'s current body), the \
           allocations backing those places in {m} do not \
           overlap.")
  (m "The machine state." : Machine)
  (pcg "The PCG data, interpreted in m's current body."
      : PcgData Place)
  := ∀∀ p p' ∈ Place, a a' ∈ Allocation .
       ‹break› p ≠ p' ∧
       ‹break› Runnable ‹m› ∧
       ‹break› hasCapability
         ‹pcg,
          currBody ‹m, lean_proof("h_Runnable")›,
          p, .exclusive› ∧
       ‹break› hasCapability
         ‹pcg,
          currBody ‹m, lean_proof("h_Runnable")›,
          p', .exclusive› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'›
       → ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty Framing (.plain "Framing")
  short
    (.plain "the PCG analysis frames non-aliasing of \
            exclusive places")
  long
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state tracked \
            by the analysis, the framing invariant holds \
            between the machine and the entry-state PCG at \
            its program counter.")
  := ∀∀ pr ∈ Program, par ∈ ProgAnalysisResults,
        m ∈ Machine .
       ‹break› validProgram ‹pr› ∧
       ‹break› describes ‹par, pr› ∧
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("h_validProgram")›, m› ∧
       ‹break› Runnable ‹m› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("h_Runnable")›,
          currPC ‹m, lean_proof("h_Runnable")››
       → ‹break› FramingInvariant
           ‹m,
            pcgEntryStateAt
              ‹par,
               currBody ‹m, lean_proof("h_Runnable")›,
               currPC ‹m, lean_proof("h_Runnable")›,
               lean_proof("h_programContains")››

defProperty NoAliasInvariant (.plain "NoAliasInvariant")
  short
    (doc! "the no-alias invariant holds between {m} and {pcg}")
  long
    (doc! "Holds when, for every pair of distinct valid \
           places in {m}'s current body backed by allocations \
           in {m}, either their corresponding PCG nodes are \
           connected in {pcg} or the backing allocations have \
           non-overlapping address ranges. The conclusion is \
           phrased as a disjunction so its contrapositive \
           reads as the disconnected-implies-disjoint \
           statement without needing a negation operator in \
           the DSL.")
  (m "The machine state." : Machine)
  (pcg "The PCG data, interpreted in m's current body."
      : PcgData Place)
  := ∀∀ p p' ∈ Place, a a' ∈ Allocation .
       ‹break› p ≠ p' ∧
       ‹break› Runnable ‹m› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("h_Runnable")›, p› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("h_Runnable")›, p'› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'›
       → ‹break› connected
           ‹pcg, placeNode ‹p›, placeNode ‹p'›› ∨
         ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty NoAlias (.plain "NoAlias")
  short
    (.plain "the PCG analysis frames non-overlap of \
            disconnected places")
  long
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state tracked \
            by the analysis, the no-alias invariant holds \
            between the machine and the entry-state PCG at \
            its program counter.")
  := ∀∀ pr ∈ Program, par ∈ ProgAnalysisResults,
        m ∈ Machine .
       ‹break› validProgram ‹pr› ∧
       ‹break› describes ‹par, pr› ∧
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("h_validProgram")›, m› ∧
       ‹break› Runnable ‹m› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("h_Runnable")›,
          currPC ‹m, lean_proof("h_Runnable")››
       → ‹break› NoAliasInvariant
           ‹m,
            pcgEntryStateAt
              ‹par,
               currBody ‹m, lean_proof("h_Runnable")›,
               currPC ‹m, lean_proof("h_Runnable")›,
               lean_proof("h_programContains")››
