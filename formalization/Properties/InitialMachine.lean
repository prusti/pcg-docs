import Properties.Aliasing
import PCG.Owned.OwnedState
import PCG.PlaceCapability
import Core.Dsl.DefTheorem

/-! # Framing invariant on the initial machine and PCG state

The initial machine of a program (`initialMachine pr h`) is constructed
by `createFrame` with no caller-provided argument values, so only local
0 (the start function's return slot) is `storageLive`'d. As a result,
the only allocation present in `(initialMachine pr h).mem` is the one
backing `Local 0`, and the only entry in the current frame's locals
map is `Local 0 ↦ <pointer to that allocation>`.

The "initial PCG state" — the entry-state PCG at block 0 of the start
function's body, as constructed by `analyzeBody` — is

    `⟨BorrowsGraph⟨mapEmpty⟩, OwnedState.initial body, BB 0, none⟩`,

where `OwnedState.initial body` puts `Local 0` at `.leaf .uninit`, every
argument local at `.leaf .deep`, and every other local at `.unallocated`.

`FramingInvariant` quantifies over places `p, p'` and allocations `a,
a'` with two `hasCapability(_, _, _, .exclusive)` and two
`hasAllocation(_, _, _)` antecedents and concludes
`Allocation.nonOverlapping a a'`. We prove that on the initial machine
+ initial PCG, this holds vacuously: any place with an allocation in
the initial machine must root at `Local 0`, but `Local 0` in
`OwnedState.initial body` has init tree `.leaf .uninit`, which yields
capability `.write` (not `.exclusive`). So
`hasCapability(_, _, p, .exclusive)` and `hasAllocation(_, p, _)`
cannot simultaneously hold for any `p`. -/

namespace Properties

open Machine StackFrame Memory Capability InitialisationState

-- `Std.HashMap` simp lemmas like `get?_insert` require `LawfulBEq` and
-- `LawfulHashable` on the key type. `Local` only derives `BEq` and
-- `Hashable`; the lawful variants are immediate from the underlying
-- `Nat` instances.
instance : LawfulBEq Local where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp [BEq.beq, instBEqLocal.beq] at h
    exact congrArg _ h
  rfl {a} := by cases a; simp [BEq.beq, instBEqLocal.beq]

instance : LawfulHashable Local where
  hash_eq {a b} h := by
    have heq : a = b := LawfulBEq.eq_of_beq h
    subst heq; rfl

/-- The initial PCG state for a function body: empty borrows graph,
    `OwnedState.initial` for the body, no transient state. -/
def initialPcg (body : Body) : PcgData Place :=
  ⟨⟨mapEmpty⟩, OwnedState.initial body, ⟨0⟩, none⟩

section Helpers

/-- The current frame of `initialMachine pr h` has its locals map
    consisting of a single entry for `Local⟨0⟩`. The pointer stored
    there has provenance `some ⟨⟨0⟩⟩` (the `AllocId` of the only
    allocation in the initial memory). The proof unfolds
    `initialMachine`, `createFrame`, `liveAndStoreArgs` (with
    `args = []`), `storageLive`, `storageDead`, and the `Memory`
    helpers. -/
private theorem initialMachine_currentFrame_locals
    (pr : Program) (h : validProgram pr) (lcl : Local) :
    let m := initialMachine pr h
    let frame := m.thread.stack.head!
    (frame.locals.get? lcl).isSome ↔ lcl = ⟨0⟩ := by
  unfold initialMachine createFrame liveAndStoreArgs
    storageLive storageDead mapGet mapEmpty mapInsert
  simp only [List.head!]
  rw [Std.HashMap.get?_insert]
  by_cases h0 : lcl = ⟨0⟩
  · subst h0; simp
  · have hne : ((⟨0⟩ : Local) == lcl) = false := by
      apply Bool.eq_false_iff.mpr
      simp [beq_iff_eq]
      intro heq; exact h0 heq.symm
    simp [hne]
    intro heq; exact h0 heq

/-- The current body of `initialMachine pr h` is the start function's
    body. -/
private theorem currBody_initialMachine
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h)) :
    currBody (initialMachine pr h) h_R = Program.startProgram pr h := by
  unfold currBody currentFrame initialMachine createFrame liveAndStoreArgs
    storageLive storageDead mapGet mapEmpty
  simp [List.head!]

/-- `evalLocal` of `initialMachine` is `some _` only for `Local⟨0⟩`. -/
private theorem evalLocal_initialMachine_local0
    (pr : Program) (h : validProgram pr)
    (lcl : Local) (h_R : Runnable (initialMachine pr h)) (pp : PlacePtr) :
    evalLocal (initialMachine pr h) lcl h_R = some pp → lcl = ⟨0⟩ := by
  intro heval
  unfold evalLocal currentFrame mapGet at heval
  -- `evalLocal` returns `(get? frame.locals lcl).bind (fun ptr => some ⟨ptr⟩)`;
  -- for it to equal `some pp`, the inner `get?` must be `some _`.
  have hSome : ((initialMachine pr h).thread.stack.head!.locals.get? lcl).isSome := by
    cases hg : (initialMachine pr h).thread.stack.head!.locals.get? lcl with
    | none =>
      exfalso
      -- `heval` uses `[lcl]?`-notation; that's defeq to `get? _ lcl`.
      change (((initialMachine pr h).thread.stack.head!.locals.get? lcl).bind
        fun ptr => some ⟨ptr⟩) = some pp at heval
      rw [hg] at heval
      simp at heval
    | some _ => simp
  exact (initialMachine_currentFrame_locals pr h lcl).mp hSome

/-- `placeAllocation` of `initialMachine` succeeds only for places
    rooted at `Local⟨0⟩`. -/
theorem placeAllocation_initialMachine_local0
    (pr : Program) (h : validProgram pr) (p : Place) (a : Allocation)
    (h_R : Runnable (initialMachine pr h)) :
    Machine.placeAllocation (initialMachine pr h) p h_R = some a →
      p.local = ⟨0⟩ := by
  intro halloc
  unfold Machine.placeAllocation evalPlace at halloc
  -- For the outer `bind` to yield `some a`, `evalLocal` must yield `some _`.
  cases hL : evalLocal (initialMachine pr h) p.local h_R with
  | none => simp [hL] at halloc
  | some pp => exact evalLocal_initialMachine_local0 pr h p.local h_R pp hL

/-- `getCapability` on the initial PCG, evaluated at a place rooted at
    `Local 0`, never returns `some .exclusive`.

    Proof sketch: trace `getCapability`'s cascade.
    `getAlloc (OwnedState.initial body) ⟨0⟩` is `some (.leaf .uninit)`
    (when `body.decls` is non-empty, which it must be if `validPlace`
    holds for a place with `local = ⟨0⟩`) or `none` (when empty);
    `treeIsInternal projs (.leaf _)` is always `false`;
    `placeIsMutablyBorrowed (BorrowsGraph⟨∅⟩) p` is `false` (no edges);
    `treeLeafCapability projs (.leaf .uninit)` is `some .write`. So
    the result is either `some .write` or `none`, never
    `some .exclusive`. -/
theorem getCapability_initialPcg_local0_not_exclusive
    (body : Body) (projs : List ProjElem)
    (h_validPlace : validPlace body ⟨⟨0⟩, projs⟩) :
    getCapability (initialPcg body) body ⟨⟨0⟩, projs⟩ h_validPlace
      ≠ some .exclusive := by
  unfold getCapability initialPcg
  simp only [PcgData.mk]
  unfold getAlloc OwnedState.initial
  cases hdecls : body.decls with
  | nil =>
    -- Empty decls: index 0 lookup is none, so getAlloc returns none,
    -- so getCapability returns none.
    simp [List.zipIdx]
  | cons d rest =>
    -- Non-empty decls: index 0 maps to .allocated (.leaf .uninit).
    -- The `getAlloc` cascade returns `some (.leaf .uninit)`.
    -- treeIsInternal _ (.leaf _) = false.
    -- placeIsMutablyBorrowed (BorrowsGraph⟨mapEmpty⟩) p: derefEdges
    --   of empty graph is [], so .any returns false.
    -- treeLeafCapability _ (.leaf .uninit) = some .write.
    -- Result: some .write ≠ some .exclusive.
    simp only [List.zipIdx, List.zipIdx_cons, List.map_cons,
               List.getElem?_cons_zero, Option.bind_some,
               beq_self_eq_true, ↓reduceIte]
    simp only [treeIsInternal, BorrowsGraph.placeIsMutablyBorrowed,
               BorrowsGraph.derefEdges, mapEmpty]
    -- For the empty BorrowsGraph (`bg.edges = ∅`), `.toList = []`,
    -- so the `.flatMap` produces `[]`, and `.any _ = false`.
    simp
    -- treeLeafCapability projs (.leaf .uninit) matches the first arm
    -- regardless of projs, returning `some .write`.
    simp only [treeLeafCapability]
    decide

end Helpers

/-- **The base-case framing invariant**: for every valid program, the
    `FramingInvariant` holds between the initial machine and the
    initial PCG state of the start function's body. -/
theorem framingInvariant_initialMachine
    (pr : Program) (h : validProgram pr) :
    FramingInvariant
      (initialMachine pr h)
      (initialPcg (Program.startProgram pr h)) := by
  intro p p' a a' _h_neq h_Runnable h_hasCap1 _h_hasCap2 h_hasAlloc1 _h_hasAlloc2
  exfalso
  -- Strategy: `hasAllocation` forces `p.local = ⟨0⟩`, and
  -- `hasCapability (initialPcg _) _ p .exclusive` is impossible for
  -- places rooted at ⟨0⟩ — the capability is `.write`, not
  -- `.exclusive`.
  -- Step 1: extract the underlying `placeAllocation` equation.
  have h_alloc_eq : Machine.placeAllocation (initialMachine pr h) p h_Runnable
      = some a := by
    cases h_hasAlloc1 with
    | fromGet heq =>
      -- Proof irrelevance handles the `h_Runnable` parameter.
      exact heq
  -- Step 2: derive `p.local = ⟨0⟩`.
  have hlocal : p.local = ⟨0⟩ :=
    placeAllocation_initialMachine_local0 pr h p a h_Runnable h_alloc_eq
  -- Step 3: rewrite the body via `currBody_initialMachine` and
  -- destructure `p` to expose `loc = ⟨0⟩`.
  have hbody := currBody_initialMachine pr h h_Runnable
  rcases p with ⟨⟨pIdx⟩, projs⟩
  simp at hlocal
  subst hlocal
  -- `hbody` rewrites the body of all dependent positions before we
  -- extract the capability equation, sidestepping the dependent
  -- rewrite issue.
  rw [hbody] at h_hasCap1
  cases h_hasCap1 with
  | fromGet h_cap_eq =>
    rename_i h_vp
    -- Step 5: conclude using the capability lemma.
    exact getCapability_initialPcg_local0_not_exclusive
      (Program.startProgram pr h) projs h_vp h_cap_eq

-- Register the theorem in the DSL so it appears in the
-- presentation export. The Lean proof is the (already
-- in-tree) `framingInvariant_initialMachine`.
defTheorem framingInvariantInitial
  (.plain "the framing invariant holds for the initial \
          machine of every valid program")
  := ∀∀ pr ∈ Program .
       validProgram ‹pr›
       → FramingInvariant
           ‹initialMachine ‹pr, lean_proof("h_validProgram")›,
            initialPcg
              ‹Program.startProgram
                 ‹pr, lean_proof("h_validProgram")›››
  proof framingInvariant_initialMachine

end Properties
