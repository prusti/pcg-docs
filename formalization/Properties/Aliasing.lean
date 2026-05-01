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
  short (prDoc, parDoc, mDoc, pDoc, p'Doc, aDoc, a'Doc) =>
    (.seq [.plain "the framing instance for ",
           prDoc, .plain ", ", parDoc, .plain ", ", mDoc,
           .plain ", places ", pDoc, .plain " and ", p'Doc,
           .plain ", allocations ", aDoc, .plain " and ",
           a'Doc])
  long (prDoc, parDoc, mDoc, pDoc, p'Doc, aDoc, a'Doc) =>
    (.seq [.plain "Holds when ", parDoc, .plain " describes ",
           prDoc, .plain ", ", mDoc, .plain " is a runnable \
           machine reachable from the initial machine of ",
           prDoc, .plain " whose currently-executing body and \
           program counter are tracked by ", parDoc,
           .plain ", the entry-state PCG at that program \
           point assigns the exclusive capability to both \
           valid places ", pDoc, .plain " and ", p'Doc,
           .plain ", and their backing allocations ", aDoc,
           .plain " and ", a'Doc, .plain " do not overlap."])
  (pr "The program." : Program)
  (par "The program-wide analysis results."
      : ProgAnalysisResults)
  (m "The machine state." : Machine)
  (p "The first place." : Place)
  (p' "The second place." : Place)
  (a "The allocation backing p." : Allocation)
  (a' "The allocation backing p'." : Allocation)
  :=
       ‹break› describes ‹par, pr› ∧
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("sorry")›, m› ∧
       ‹break› Runnable ‹m› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p'› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("sorry")›,
          currPC ‹m, lean_proof("sorry")›› ∧
       ‹break› hasCapability
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          currBody ‹m, lean_proof("sorry")›,
          p, .exclusive› ∧
       ‹break› hasCapability
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          currBody ‹m, lean_proof("sorry")›,
          p', .exclusive› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'› ∧
       ‹break› Allocation.nonOverlapping ‹a, a'›

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
       ‹break› Framing' ‹pr, par, m, p, p', a, a'›

defProperty NoAlias' (.plain "NoAlias'")
  short (prDoc, parDoc, mDoc, pDoc, p'Doc, aDoc, a'Doc) =>
    (.seq [.plain "the no-alias instance for ",
           prDoc, .plain ", ", parDoc, .plain ", ", mDoc,
           .plain ", places ", pDoc, .plain " and ", p'Doc,
           .plain ", allocations ", aDoc, .plain " and ",
           a'Doc])
  long (prDoc, parDoc, mDoc, pDoc, p'Doc, aDoc, a'Doc) =>
    (.seq [.plain "Holds when ", parDoc, .plain " describes ",
           prDoc, .plain ", ", mDoc, .plain " is a runnable \
           machine reachable from the initial machine of ",
           prDoc, .plain " whose currently-executing body and \
           program counter are tracked by ", parDoc,
           .plain ", and for the two valid places ", pDoc,
           .plain " and ", p'Doc, .plain " backed by \
           allocations ", aDoc, .plain " and ", a'Doc,
           .plain ", either their PCG nodes are connected in \
           the entry-state PCG at that program point or the \
           allocations have non-overlapping address ranges. \
           The final clause is phrased as a disjunction so the \
           contrapositive reads as the disconnected-implies-\
           disjoint statement without needing a negation \
           operator in the DSL."])
  (pr "The program." : Program)
  (par "The program-wide analysis results."
      : ProgAnalysisResults)
  (m "The machine state." : Machine)
  (p "The first place." : Place)
  (p' "The second place." : Place)
  (a "The allocation backing p." : Allocation)
  (a' "The allocation backing p'." : Allocation)
  :=
       ‹break› describes ‹par, pr› ∧
       ‹break› Reachable
         ‹initialMachine
            ‹pr, lean_proof("sorry")›, m› ∧
       ‹break› Runnable ‹m› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p› ∧
       ‹break› validPlace
         ‹currBody ‹m, lean_proof("sorry")›, p'› ∧
       ‹break› programContains
         ‹par,
          currBody ‹m, lean_proof("sorry")›,
          currPC ‹m, lean_proof("sorry")›› ∧
       ‹break› hasAllocation ‹m, p, a› ∧
       ‹break› hasAllocation ‹m, p', a'› ∧
       ‹break› (connected
         ‹pcgEntryStateAt
            ‹par,
             currBody ‹m, lean_proof("sorry")›,
             currPC ‹m, lean_proof("sorry")›,
             lean_proof("sorry")›,
          placeNode ‹p›, placeNode ‹p'›› ∨
       ‹break› Allocation.nonOverlapping ‹a, a'›)

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
        p p' ∈ Place, a a' ∈ Allocation .
       ‹break› NoAlias' ‹pr, par, m, p, p', a, a'›
