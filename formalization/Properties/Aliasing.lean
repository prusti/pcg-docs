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
exclusive places from sharing an allocation; `Connected`
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

`Connected` mirrors `Framing`'s split: `ConnectedInvariant` is a
stand-alone property over `(m, pcg)` that asserts the
disconnected-implies-disjoint conclusion for any pair of valid
places, and the unprimed `Connected` sets up the program-level
antecedents (analysis describes program, reachability,
runnability, program-contains) that ground the
`pcgEntryStateAt` lookup, and applies `ConnectedInvariant`. -/

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
          currBody ‹m, proof[h_Runnable]›,
          p, .exclusive› ∧
       ‹break› hasCapability
         ‹pcg,
          currBody ‹m, proof[h_Runnable]›,
          p', .exclusive› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'›
       → ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty FramingInvariant' (.plain "FramingInvariant'")
  short
    (doc! "the framing invariant holds for {m} against the \
           entry-state PCG that {par} stores at {m}'s current \
           program counter")
  long
    (doc! "Specialises #FramingInvariant by resolving the PCG \
           argument from program-wide analysis results: when \
           {par} records analysis results for {m}'s \
           currently-executing body and program counter, the \
           framing invariant holds between {m} and the \
           entry-state PCG {par} stores there.")
  (m "The machine state." : Machine)
  (par "The program-wide analysis results."
      : ProgAnalysisResults)
  := ‹break› Runnable ‹m› ∧
     ‹break› programContains
       ‹par,
        currBody ‹m, proof[h_Runnable]›,
        currPC ‹m, proof[h_Runnable]›› ∧
     ‹break› FramingInvariant
       ‹m,
        pcgEntryStateAt
          ‹par,
           currBody ‹m, proof[h_Runnable]›,
           currPC ‹m, proof[h_Runnable]›,
           proof[h_programContains]››

defProperty Framing (.plain "Framing")
  short
    (.plain "the PCG analysis frames non-aliasing of \
            exclusive places")
  long
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state, the \
            framing invariant holds between the machine and \
            the entry-state PCG at its program counter.")
  := ∀∀ par ∈ ProgAnalysisResults, m ∈ Machine .
       ‹break› Runnable ‹m› ∧
       ‹break› describes ‹par, prog ‹m›› ∧
       -- `validProgram (prog m)` is the second conjunct of
       -- `Runnable`'s body; project it directly with
       -- `h_Runnable.2.1` to discharge `initialMachine`'s
       -- precondition without a separate antecedent.
       ‹break› Reachable
         ‹initialMachine
            ‹prog ‹m›, proof[h_Runnable.2.1]›, m›
       → ‹break› FramingInvariant' ‹m, par›

defProperty FramingInd (.plain "FramingInd")
  short
    (.plain "the framing invariant is preserved by a single \
            #[Step] transition")
  long
    (doc! "The inductive step of #[Framing]'s soundness: if \
           the current machine is runnable and reached by a \
           single #[Step] from a predecessor machine state \
           that itself satisfies #[FramingInvariant'] \
           against the same program-wide analysis results, \
           then #[FramingInvariant'] also holds at the \
           current machine. Pairing this with the base case \
           (#[FramingInvariant'] on the initial machine) and \
           induction on #[Reachable]'s reflexive-transitive \
           closure of #[Step] gives the full #[Framing].")
  := ∀∀ par ∈ ProgAnalysisResults,
        m' m ∈ Machine .
       ‹break› Runnable ‹m› ∧
       ‹break› describes ‹par, prog ‹m›› ∧
       ‹break› Step ‹m', m› ∧
       ‹break› FramingInvariant' ‹m', par›
       → ‹break› FramingInvariant' ‹m, par›

defProperty ConnectedInvariant (.plain "ConnectedInvariant")
  short
    (doc! "the connected invariant holds between {m} and {pcg}")
  long
    (doc! "Holds when, for every pair of distinct valid \
           places in {m}'s current body that the PCG \
           actually tracks (i.e. that lie in #places of \
           {pcg}) and which are backed by allocations in \
           {m}, either their PCG nodes are connected in \
           {pcg} or the backing allocations have \
           non-overlapping address ranges. The conclusion \
           is phrased as a disjunction so its \
           contrapositive reads as the \
           disconnected-implies-disjoint statement without \
           needing a negation operator in the DSL. The \
           `p ∈ places pcg` antecedents constrain the \
           property to places the PCG actually tracks: \
           places that don't appear in #places of {pcg} \
           carry no analysis guarantee, and the invariant \
           holds for them vacuously (the standard pattern \
           when the PCG hasn't yet unpacked far enough to \
           mention them).")
  (m "The machine state." : Machine)
  (pcg "The PCG data, interpreted in m's current body."
      : PcgData Place)
  := ∀∀ p p' ∈ Place, a a' ∈ Allocation .
       ‹break› p ≠ p' ∧
       ‹break› Runnable ‹m› ∧
       ‹break› validPlace
         ‹currBody ‹m, proof[h_Runnable]›, p› ∧
       ‹break› validPlace
         ‹currBody ‹m, proof[h_Runnable]›, p'› ∧
       ‹break› p ∈ places ‹pcg› ∧
       ‹break› p' ∈ places ‹pcg› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'›
       → ‹break› connected
           ‹pcg, placeNode ‹p›, placeNode ‹p'›› ∨
         ‹break› Allocation.nonOverlapping ‹a, a'›

defProperty Connected (.plain "Connected")
  short
    (.plain "the PCG analysis frames non-overlap of \
            disconnected places")
  long
    (.plain "If analysis results describe a program, then \
            at any reachable runnable machine state tracked \
            by the analysis, the connected invariant holds \
            between the machine and the entry-state PCG at \
            its program counter.")
  := ∀∀ par ∈ ProgAnalysisResults, m ∈ Machine .
       ‹break› Runnable ‹m› ∧
       ‹break› describes ‹par, prog ‹m›› ∧
       -- See Framing for why `h_Runnable.2.1` discharges
       -- `initialMachine`'s `validProgram` precondition.
       ‹break› Reachable
         ‹initialMachine
            ‹prog ‹m›, proof[h_Runnable.2.1]›, m› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, proof[h_Runnable]›,
          currPC ‹m, proof[h_Runnable]››
       → ‹break› ConnectedInvariant
           ‹m,
            pcgEntryStateAt
              ‹par,
               currBody ‹m, proof[h_Runnable]›,
               currPC ‹m, proof[h_Runnable]›,
               proof[h_programContains]››
