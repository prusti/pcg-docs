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

`NoAlias` is still stated in two layers: a primed instance
(`NoAlias'`) takes the witnesses (`pr`, `par`, `m`, `p`, `p'`,
`a`, `a'`) as explicit parameters and asserts the implication
for that one tuple, and the unprimed property universally
quantifies over them and applies the primed one. This split
lets proofs target a specific case (for instance, the base case
where `m = initialMachine pr`) without having to re-quantify. -/

defProperty FramingInvariant (.plain "FramingInvariant")
  short
    (doc! "the framing invariant holds between {m} and {pcg}")
  long
    (doc! "Holds when, for every pair of places assigned the \
           exclusive capability by {pcg} (interpreted in {m}'s \
           current body), the allocations backing those places \
           in {m} do not overlap.")
  (m "The machine state." : Machine)
  (pcg "The PCG data, interpreted in m's current body."
      : PcgData Place)
  := ∀∀ p p' ∈ Place, a a' ∈ Allocation .
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

defProperty NoAlias' (.plain "NoAlias'")
  short
    (doc! "the no-alias instance for {pr}, {par}, {m}, \
           places {p} and {p'}, \
           allocations {a} and {a'}")
  long
    (doc! "If {par} describes {pr}, {m} is a runnable machine \
           reachable from the initial machine of {pr} whose \
           currently-executing body and program counter are \
           tracked by {par}, and the two valid places {p} \
           and {p'} are backed by allocations {a} and {a'}, \
           then either their PCG nodes are connected in the \
           entry-state PCG at that program point or the \
           allocations have non-overlapping address ranges. \
           The conclusion is phrased as a disjunction so the \
           contrapositive reads as the disconnected-implies-\
           disjoint statement without needing a negation \
           operator in the DSL.")
  (pr "The program." : Program)
  (par "The program-wide analysis results."
      : ProgAnalysisResults)
  (m "The machine state." : Machine)
  (p "The first place." : Place)
  (p' "The second place." : Place)
  (a "The allocation backing p." : Allocation)
  (a' "The allocation backing p'." : Allocation)
  :=
       ‹break› validProgram ‹pr› ∧
       ‹break› describes ‹par, pr› ∧
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("h_validProgram")›, m› ∧
       ‹break› Runnable ‹m› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("h_Runnable")›, p› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("h_Runnable")›, p'› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("h_Runnable")›,
          currPC ‹m, lean_proof("h_Runnable")›› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'›
       → ‹break› connected
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("h_Runnable")›,
             currPC ‹m, lean_proof("h_Runnable")›,
             lean_proof("h_programContains")›,
          placeNode ‹p›, placeNode ‹p'›› ∨
       ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty NoAlias (.plain "NoAlias")
  short
    (.plain "the PCG analysis frames non-overlap of \
            disconnected places")
  long
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
        p p' ∈ Place, a a' ∈ Allocation .
       ‹break› NoAlias' ‹pr, par, m, p, p', a, a'›
