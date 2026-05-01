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

Both properties are stated in two layers: a primed instance
(`Framing'` / `NoAlias'`) takes the witnesses (`pr`, `par`, `m`,
`p`, `p'`, `a`, `a'`) as explicit parameters and asserts the
implication for that one tuple, and the unprimed property
universally quantifies over them and applies the primed one.
This split lets proofs target a specific case (for instance, the
base case where `m = initialMachine pr`) without having to
re-quantify. -/

defProperty Framing' (.plain "Framing'")
  short
    (doc! "the framing instance for {pr}, {par}, {m}, \
           places {p} and {p'}, \
           allocations {a} and {a'}")
  long
    (doc! "If {par} describes {pr}, {m} is a \
           runnable machine reachable from the initial machine \
           of {pr} whose currently-executing body and \
           program counter are tracked by {par}, the \
           entry-state PCG at that program point assigns the \
           exclusive capability to both valid places {p} \
           and {p'}, and {a}, {a'} back the two places, \
           then the allocations have non-overlapping address \
           ranges.")
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
       ‹break› hasCapability
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("h_Runnable")›,
             currPC ‹m, lean_proof("h_Runnable")›,
             lean_proof("h_programContains")›,
          currBody ‹m, lean_proof("h_Runnable")›,
          p, .exclusive› ∧
       ‹break› hasCapability
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("h_Runnable")›,
             currPC ‹m, lean_proof("h_Runnable")›,
             lean_proof("h_programContains")›,
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
            at any reachable runnable machine state, two \
            places that the entry-state PCG at the machine's \
            program counter assigns the exclusive capability \
            are backed by allocations whose address ranges \
            do not overlap.")
  := ∀∀ pr ∈ Program, par ∈ ProgAnalysisResults,
        m ∈ Machine,
        p p' ∈ Place, a a' ∈ Allocation .
       ‹break› Framing' ‹pr, par, m, p, p', a, a'›

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
