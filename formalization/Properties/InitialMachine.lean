import Properties.Aliasing
import PCG.Owned.OwnedState
import PCG.PlaceCapability
import Core.Dsl.DefTheorem

/-! # Framing and Connected invariants on the initial machine

The initial machine of a program (`initialMachine pr h`) is constructed
by `createFrame` with no caller-provided argument values, so only local
0 (the start function's return slot) is `storageLive`'d. As a result,
**there is exactly one allocation** in `(initialMachine pr h).mem` —
the one backing `Local 0` — and the only entry in the current frame's
locals map is `Local 0 ↦ <pointer to that allocation>`.

The "initial PCG state" — the entry-state PCG at block 0 of the start
function's body, as constructed by `analyzeBody` — is

    `⟨BorrowsGraph⟨mapEmpty⟩, OwnedState.initial body, BB 0, none⟩`,

where `OwnedState.initial body` puts `Local 0` at `.leaf .uninit`,
every argument local at `.leaf .deep`, and every other local at
`.unallocated`.

Both base-case proofs (`framingInvariant_initialMachine` and
`connectedInvariant_initialMachine`) are organised around the
**single-allocation** observation: any two `hasAllocation _ _ _`
witnesses in the initial machine name the same backing allocation
(see `hasAllocation_initialMachine_eq`), so `a = a'` is forced
upfront and the remaining argument is invariant-specific. -/

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
    consisting of a single entry for `Local⟨0⟩`. -/
private theorem initialMachine_currentFrame_locals
    (pr : Program) (h : validProgram pr) (lcl : Local) :
    let m := initialMachine pr h
    let frame := m.thread.stack.head!
    (frame.locals.get? lcl).isSome ↔ lcl = ⟨0⟩ := by
  -- After the `validStackFrame` overhaul, `storageDead` uses
  -- `match heq : … with` to recover its precondition, which
  -- `unfold storageLive storageDead ; simp` no longer pushes
  -- through to a `Std.HashMap.get?_insert` rewrite. Left as
  -- `sorry` until the InitialMachine proofs are updated.
  sorry

/-- The current body of `initialMachine pr h` is the start function's
    body. -/
private theorem currBody_initialMachine
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h)) :
    currBody (initialMachine pr h) h_R = Program.startProgram pr h := by
  -- See `initialMachine_currentFrame_locals` above for why this
  -- proof is currently a `sorry`.
  sorry

/-- **Single-allocation lemma**: the initial machine has exactly one
    allocation. `createFrame` invoked with no caller arguments runs
    `liveAndStoreArgs []` (a no-op) and a single `storageLive` for
    `Local 0`, so `Memory.allocate` is called exactly once on an
    initially-empty memory. -/
theorem mem_initialMachine_length_one
    (pr : Program) (h : validProgram pr) :
    (initialMachine pr h).mem.allocs.length = 1 := by
  -- After the `validStackFrame` overhaul, `storageDead` uses
  -- `match heq : … with` to recover its precondition. The
  -- former `unfold … storageLive storageDead … ; simp` proof
  -- doesn't push the new shape through; left as `sorry` until
  -- the InitialMachine proofs are updated to handle it.
  sorry

-- Corollary of single allocation: every successful `mem.allocs`
-- lookup in the initial machine returns the same allocation —
-- `m.mem.allocs[0]!` — when the index is `0`, and the
-- `Inhabited`-default otherwise. We do not need to distinguish the
-- two: any two lookups whose results "match up" via `placeAllocation`
-- agree by `evalPlace_provenance_initialMachine`.

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
  cases hL : evalLocal (initialMachine pr h) p.local h_R with
  | none => simp [hL] at halloc
  | some pp => exact evalLocal_initialMachine_local0 pr h p.local h_R pp hL

/-- `getCapability` on the initial PCG, evaluated at a place rooted at
    `Local 0`, never returns `some .exclusive`. -/
theorem getCapability_initialPcg_local0_not_exclusive
    (body : Body) (projs : List ProjElem)
    (h_validPlace : validPlace body ⟨⟨0⟩, projs⟩) :
    getCapability (initialPcg body) body ⟨⟨0⟩, projs⟩ h_validPlace
      ≠ some .exclusive := by
  unfold getCapability initialPcg
  unfold getAlloc OwnedState.initial
  cases hdecls : body.decls with
  | nil =>
    simp [List.zipIdx]
  | cons d rest =>
    -- Non-empty decls: index 0 maps to .allocated (.leaf .uninit).
    -- The `getAlloc` cascade returns `some (.leaf .uninit)`.
    -- treeIsInternal _ (.leaf _) = false.
    -- placeIsMutablyBorrowed (BorrowsGraph⟨mapEmpty⟩) p: derefEdges
    --   of empty graph is [], so .any returns false.
    -- treeLeafCapability _ (.leaf .uninit) = some .write.
    -- Result: some .write ≠ some .exclusive.
    simp only [List.zipIdx, List.map_cons,
               List.getElem?_cons_zero, Option.bind_some,
               beq_self_eq_true, ↓reduceIte]
    simp only [treeIsInternal, BorrowsGraph.placeIsMutablyBorrowed,
               BorrowsGraph.derefEdges, mapEmpty]
    simp
    simp only [treeLeafCapability]
    decide

/-- The provenance of any successful `evalPlace` in
    `initialMachine pr h` is `some ⟨⟨0⟩⟩` — the `AllocId` of the
    unique allocation.

    Proof sketch: `evalPlace` runs `evalLocal` on `p.local`, then
    walks `p.projection` via `evalProjs`. The base pointer comes
    from the locals map; in `initialMachine` the only entry is for
    `Local⟨0⟩` with provenance `some ⟨⟨0⟩⟩` (per the construction
    in `storageLive`). The projection arms (`evalProjs`'s `.field`
    / `.downcast` / `.index` cases) preserve provenance verbatim;
    the `.deref` arm needs `decodePtr` to succeed on memory bytes,
    but `initialMachine` has uninit bytes only, so `decodePtr`
    returns `none` and `evalProjs` short-circuits.

    A full structural-induction proof on `p.projection` follows
    those observations; the statement is isolated here so the
    higher-level single-allocation argument
    (`hasAllocation_initialMachine_eq`) can quote it directly. -/
private theorem evalPlace_provenance_initialMachine
    (pr : Program) (h : validProgram pr) (p : Place)
    (h_R : Runnable (initialMachine pr h)) (pp : PlacePtr) (ty : Ty)
    (heval : evalPlace (initialMachine pr h) p h_R = some ⟨pp, ty⟩) :
    pp.ptr.provenance = some ⟨⟨0⟩⟩ := by
  sorry

/-- **The key shared lemma**: any two `hasAllocation _ _ _` witnesses
    in the initial machine name the same backing allocation. Direct
    consequence of the single-allocation lemma — both lookups bottom
    out at `m.mem.allocs[0]!`. -/
theorem hasAllocation_initialMachine_eq
    (pr : Program) (h : validProgram pr)
    {p p' : Place} {a a' : Allocation}
    (h_alloc_p : hasAllocation (initialMachine pr h) p a)
    (h_alloc_p' : hasAllocation (initialMachine pr h) p' a') :
    a = a' := by
  cases h_alloc_p with
  | fromGet hp_eq =>
    rename_i h_R_p
    cases h_alloc_p' with
    | fromGet hp'_eq =>
      rename_i h_R_p'
      unfold Machine.placeAllocation at hp_eq hp'_eq
      cases hep : evalPlace (initialMachine pr h) p h_R_p with
      | none => simp [hep] at hp_eq
      | some pair =>
        rcases pair with ⟨pp, ty⟩
        cases hep' : evalPlace (initialMachine pr h) p' h_R_p' with
        | none => simp [hep'] at hp'_eq
        | some pair' =>
          rcases pair' with ⟨pp', ty'⟩
          have hprov := evalPlace_provenance_initialMachine
            pr h p h_R_p pp ty hep
          have hprov' := evalPlace_provenance_initialMachine
            pr h p' h_R_p' pp' ty' hep'
          simp [hep, hprov, Option.bind] at hp_eq
          simp [hep', hprov', Option.bind] at hp'_eq
          subst hp_eq
          subst hp'_eq
          rfl

end Helpers

/-! ## Framing-invariant base case

The proof has two ingredients, both rooted in single-allocation:

1. `hasAllocation_initialMachine_eq` collapses `a` and `a'` to the
   same allocation, so the conclusion `nonOverlapping a a'`
   reduces to `nonOverlapping a a` — false for any non-empty
   allocation.
2. To finish, we observe that the antecedent
   `hasCapability(_, _, p, .exclusive)` is itself unsatisfiable in
   the initial PCG — `getCapability` on a place rooted at
   `Local 0` returns at most `some .write` (because
   `OwnedState.initial body` assigns `Local 0` the `.leaf .uninit`
   tree). The vacuity of the antecedent discharges the goal. -/

/-- **The base-case framing invariant**: for every valid program, the
    `FramingInvariant` holds between the initial machine and the
    initial PCG state of the start function's body. -/
theorem framingInvariant_initialMachine
    (pr : Program) (h : validProgram pr) :
    FramingInvariant
      (initialMachine pr h)
      (initialPcg (Program.startProgram pr h)) := by
  intro p p' a a' _h_neq h_Runnable h_hasCap1 _h_hasCap2
        h_hasAlloc1 h_hasAlloc2
  exfalso
  -- Step 1 (single-allocation): both `hasAllocation` witnesses
  -- name the same backing allocation. This step is invariant-
  -- agnostic and shared with the connected-invariant proof.
  have _h_a_eq : a = a' :=
    hasAllocation_initialMachine_eq pr h h_hasAlloc1 h_hasAlloc2
  -- Step 2 (cap-not-exclusive): from `hasAllocation` we know
  -- `p.local = ⟨0⟩`, and `getCapability` on a place rooted at
  -- `⟨0⟩` returns `.write`, never `.exclusive`. The
  -- `hasCapability(.exclusive)` antecedent is therefore
  -- unsatisfiable.
  have h_alloc_eq : Machine.placeAllocation (initialMachine pr h)
      p h_Runnable = some a := by
    cases h_hasAlloc1 with | fromGet heq => exact heq
  have hlocal : p.local = ⟨0⟩ :=
    placeAllocation_initialMachine_local0 pr h p a h_Runnable h_alloc_eq
  have hbody := currBody_initialMachine pr h h_Runnable
  rcases p with ⟨⟨pIdx⟩, projs⟩
  simp at hlocal
  subst hlocal
  rw [hbody] at h_hasCap1
  cases h_hasCap1 with
  | fromGet h_cap_eq =>
    rename_i h_vp
    exact getCapability_initialPcg_local0_not_exclusive
      (Program.startProgram pr h) projs h_vp h_cap_eq

-- Register the framing-invariant theorem in the DSL so it
-- appears in the presentation export.
defTheorem framingInvariantInitial
  (.plain "the framing invariant holds for the initial \
          machine of every valid program")
  := ∀∀ pr ∈ Program .
       validProgram pr
       → FramingInvariant
           (initialMachine pr proof[h_validProgram]) (initialPcg
              (Program.startProgram
                 pr proof[h_validProgram]))
  proof framingInvariant_initialMachine

/-! ## Connected-invariant base case

The strengthened `ConnectedInvariant` carries `p ∈ places pcg`
and `p' ∈ places pcg` antecedents. `places` includes every
place along an allocated local's init tree (via `itPlaces`)
together with every place endpoint of a deref or borrow edge
in the borrows graph.

For the initial PCG, `OwnedState.initial body` assigns each
allocated local a `.leaf` init tree, so `itPlaces` produces a
single root place `⟨local, []⟩` per allocated local. The borrows
graph is empty (no deref or borrow edges contribute). So
`p ∈ places (initialPcg body)` forces `p.projection = []`.

Combined with `hasAllocation_initialMachine` (which forces
`p.local = ⟨0⟩`), the antecedent collapses both `p` and `p'`
to `⟨⟨0⟩, []⟩` — contradicting the `p ≠ p'` antecedent of
`ConnectedInvariant`. -/

/-- A place tracked by the initial PCG must be a bare local
    (empty projection): the only places in the initial PCG
    are the roots of each allocated local's `.leaf` init
    tree. -/
theorem places_initialPcg_root
    (body : Body) (p : Place)
    (h_places : p ∈ places (initialPcg body)) :
    p.projection = [] := by
  -- `places` for `initialPcg` is the union of the
  -- owned-state walk and the deref/borrow edge walk. The
  -- initial borrows graph is empty, so the edge-side
  -- contribution is empty. The owned-state walk runs
  -- `itPlaces` on each allocated local's `.leaf` init tree;
  -- `itPlaces (.leaf _) base [] = {⟨base, []⟩}`. So the
  -- only places in `places (initialPcg body)` are
  -- `⟨⟨i⟩, []⟩` for allocated locals, forcing
  -- `p.projection = []`.
  sorry

/-- **Singleton lemma**: under the antecedents of
    `ConnectedInvariant` for the initial machine, the set of
    places `p` that satisfy `p ∈ places (initialPcg ..)` *and*
    `Machine.placeAllocation (initialMachine ..) p _ = some _`
    is the singleton `{⟨⟨0⟩, []⟩}`.

    Combines `places_initialPcg_root` (the PCG side forces
    `p.projection = []`, since the initial PCG has only
    `.leaf` init trees and an empty borrows graph) with
    `placeAllocation_initialMachine_local0` (the machine side
    forces `p.local = ⟨0⟩`, since `Local 0` is the only
    allocated local in the initial machine). -/
theorem place_initialMachine_initialPcg_eq_root
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h))
    (p : Place) (a : Allocation)
    (h_places : p ∈
      places (initialPcg (Program.startProgram pr h)))
    (h_alloc : Machine.placeAllocation
      (initialMachine pr h) p h_R = some a) :
    p = ⟨⟨0⟩, []⟩ := by
  cases p with
  | mk loc projs =>
    have h_proj : projs = [] :=
      places_initialPcg_root (Program.startProgram pr h)
        ⟨loc, projs⟩ h_places
    have h_local : loc = ⟨0⟩ :=
      placeAllocation_initialMachine_local0
        pr h ⟨loc, projs⟩ a h_R h_alloc
    cases h_proj
    cases h_local
    rfl

/-- **The base-case connected invariant**: for every valid
    program, the strengthened `ConnectedInvariant` holds
    between the initial machine and the initial PCG state of
    the start function's body.

    Proof: by the singleton lemma above, the conjunction of
    the `p ∈ places pcg` and `hasAllocation _ p _`
    antecedents pins both `p` and `p'` to `⟨⟨0⟩, []⟩`,
    contradicting `p ≠ p'`. -/
theorem connectedInvariant_initialMachine
    (pr : Program) (h : validProgram pr) :
    ConnectedInvariant
      (initialMachine pr h)
      (initialPcg (Program.startProgram pr h)) := by
  intro p p' a a' h_distinct h_Runnable _h_validPlace _h_validPlace'
        h_places h_places' h_alloc_p h_alloc_p'
  exfalso
  -- Extract the underlying `Machine.placeAllocation` equations.
  have h_alloc_eq_p : Machine.placeAllocation
      (initialMachine pr h) p h_Runnable = some a := by
    cases h_alloc_p with | fromGet heq => exact heq
  have h_alloc_eq_p' : Machine.placeAllocation
      (initialMachine pr h) p' h_Runnable = some a' := by
    cases h_alloc_p' with | fromGet heq => exact heq
  -- Apply the singleton lemma to both `p` and `p'`.
  have hp : p = ⟨⟨0⟩, []⟩ :=
    place_initialMachine_initialPcg_eq_root
      pr h h_Runnable p a h_places h_alloc_eq_p
  have hp' : p' = ⟨⟨0⟩, []⟩ :=
    place_initialMachine_initialPcg_eq_root
      pr h h_Runnable p' a' h_places' h_alloc_eq_p'
  exact h_distinct (hp.trans hp'.symm)

-- Register the connected-invariant theorem in the DSL.
defTheorem connectedInvariantInitial
  (.plain "the connected invariant holds for the initial \
          machine of every valid program")
  := ∀∀ pr ∈ Program .
       validProgram pr
       → ConnectedInvariant
           (initialMachine pr proof[h_validProgram]) (initialPcg
              (Program.startProgram
                 pr proof[h_validProgram]))
  proof connectedInvariant_initialMachine

end Properties
