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
    cases a; cases b; simp [BEq.beq, instBEqLocal.beq] at h
    exact congrArg _ h
  rfl {a} := by cases a; simp [BEq.beq, instBEqLocal.beq]

instance : LawfulHashable Local where
  hash_eq {a b} h := by cases LawfulBEq.eq_of_beq h; rfl

section Helpers

private theorem mapGet_mapEmpty {κ ν : Type} [BEq κ] [Hashable κ]
    (k : κ) : mapGet (mapEmpty : Map κ ν) k = .none := by
  unfold mapGet mapEmpty
  exact Std.HashMap.getElem?_empty

/-- `storageDead` is a no-op when the local being deallocated is
    absent from the frame's locals map. The new `validStackFrame`
    overhaul made `storageDead` discharge its `validPtr` precondition
    via a `match heq : mapGet … with` form; on an absent lookup the
    match collapses to its `.none` arm, leaving the frame and memory
    unchanged. -/
private theorem storageDead_of_mapGet_eq_none
    {frame : StackFrame} {mem : Memory} {l : Local}
    {h1 : validStackFrame mem frame} {h2 : validLocal frame.body l}
    (hg : mapGet frame.locals l = .none) :
    StackFrame.storageDead frame mem l h1 h2 = ⟨frame, mem⟩ := by
  unfold StackFrame.storageDead
  split
  · rfl
  · next ptr heq => rw [hg] at heq; cases heq

/-- Specialisation of `storageDead_of_mapGet_eq_none` for a frame whose
    locals map is the empty map — applies to the very first call inside
    `createFrame` (where the initial frame has `locals := mapEmpty`). -/
private theorem storageDead_initFrame_mapEmpty
    {body : Body} {pc : Location} {mem : Memory} {l : Local}
    {h1 : validStackFrame mem ⟨body, pc, mapEmpty⟩}
    {h2 : validLocal body l} :
    StackFrame.storageDead ⟨body, pc, mapEmpty⟩ mem l h1 h2
      = (⟨body, pc, mapEmpty⟩, mem) :=
  storageDead_of_mapGet_eq_none (mapGet_mapEmpty _)

/-- `liveAndStoreArgs []` is the identity — it neither allocates new
    locals nor mutates the supplied memory. The proof arguments are
    irrelevant; consumers can supply `sorry`-shaped placeholders or
    real witnesses. -/
private theorem liveAndStoreArgs_nil
    (k : Nat) (frame : StackFrame) (mem : Memory)
    (h1 : validMemory mem) (h2 : validStackFrame mem frame)
    (h3 : StackFrame.localsAllocated frame 1 k)
    (h4 : k + ([] : List Value).length ≤ frame.body.decls.length) :
    liveAndStoreArgs [] k frame mem h1 h2 h3 h4 = (frame, mem) := by
  unfold liveAndStoreArgs; rfl

/-- The current frame of `initialMachine pr h` has its locals map
    consisting of a single entry for `Local⟨0⟩`. -/
private theorem initialMachine_currentFrame_locals
    (pr : Program) (h : validProgram pr) (lcl : Local) :
    let m := initialMachine pr h
    let frame := m.thread.stack.head!
    (frame.locals.get? lcl).isSome ↔ lcl = ⟨0⟩ := by
  -- The initial machine's stack head is the frame produced by
  -- `storageLive ⟨body, START, mapEmpty⟩ ⟨[]⟩ ⟨0⟩`, whose locals
  -- map is `mapInsert mapEmpty ⟨0⟩ ptr` for some `ptr`. The
  -- `storageDead` call inside `storageLive` is a no-op because
  -- `mapGet mapEmpty ⟨0⟩ = .none` (see
  -- `storageDead_of_mapGet_eq_none`). We rewrite that step
  -- explicitly, then reduce the resulting `get?_insert` lookup.
  unfold initialMachine Machine.createFrame
    StackFrame.storageLive
  simp only [storageDead_initFrame_mapEmpty, liveAndStoreArgs_nil]
  simp only [List.head!]
  unfold mapInsert
  rw [Std.HashMap.get?_insert]
  by_cases h0 : lcl = ⟨0⟩
  · subst h0; simp
  · have hne : ((⟨0⟩ : Local) == lcl) = false := by
      apply Bool.eq_false_iff.mpr
      simp [beq_iff_eq]
      intro heq; exact h0 heq.symm
    simp [hne, mapEmpty]
    exact h0

/-- The current body of `initialMachine pr h` is the start function's
    body. -/
private theorem currBody_initialMachine
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h)) :
    currBody (initialMachine pr h) h_R = Program.startProgram pr h := by
  unfold currBody currentFrame initialMachine Machine.createFrame
    StackFrame.storageLive
  simp only [storageDead_initFrame_mapEmpty, liveAndStoreArgs_nil]
  simp [List.head!]

/-- **Single-allocation lemma**: the initial machine has exactly one
    allocation. `createFrame` invoked with no caller arguments runs
    `liveAndStoreArgs []` (a no-op) and a single `storageLive` for
    `Local 0`, so `Memory.allocate` is called exactly once on an
    initially-empty memory. -/
theorem mem_initialMachine_length_one
    (pr : Program) (h : validProgram pr) :
    (initialMachine pr h).mem.allocs.length = 1 := by
  unfold initialMachine Machine.createFrame
    StackFrame.storageLive
  simp only [storageDead_initFrame_mapEmpty, liveAndStoreArgs_nil]
  unfold Memory.allocate
  simp

-- Corollary of single allocation: every successful `mem.allocs`
-- lookup in the initial machine returns the same allocation —
-- `m.mem.allocs[0]!` — when the index is `0`, and the
-- `Inhabited`-default otherwise. We do not need to distinguish the
-- two: any two lookups whose results "match up" via `placeAllocation`
-- agree by `evalPlace_provenance_initialMachine`.

/-- Project the `Machine.placeAllocation` equation out of a
    `hasAllocation` witness. The inductive constructor `fromGet`
    carries this equation as its sole field; we expose it as a
    helper to avoid repeating the `cases h with | fromGet heq` /
    `exact heq` two-liner across base-case proofs. The implicit
    `Runnable` proof inside the constructor coincides with the
    `h_R` argument by proof irrelevance. -/
private theorem placeAllocation_of_hasAllocation
    {m : Machine} {p : Place} {a : Allocation} (h_R : Runnable m)
    (h : hasAllocation m p a) :
    Machine.placeAllocation m p h_R = some a := by
  cases h with | fromGet heq => exact heq

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
    getCapability (PcgData.init body) body ⟨⟨0⟩, projs⟩ h_validPlace
      ≠ some .exclusive := by
  unfold getCapability PcgData.init
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

/-- The locals map of `initialMachine` binds `Local⟨0⟩` to a thin
    pointer whose provenance is the unique allocation `AllocId⟨0⟩`.

    Following the same pattern as `initialMachine_currentFrame_locals`,
    we unfold the chain `initialMachine` → `createFrame` → `storageLive`,
    collapse the no-op `storageDead` (via `storageDead_initFrame_mapEmpty`)
    and the no-op `liveAndStoreArgs []` (via `liveAndStoreArgs_nil`), so
    the head frame's locals map becomes `mapInsert mapEmpty ⟨0⟩ ptr`
    where `ptr = ⟨addr, some ⟨allocId⟩⟩` and `allocId = ⟨0⟩` (the
    initial memory has no allocations, so `Memory.allocate`'s freshly
    minted id is `AllocId⟨0⟩`). The `get?` on that map for `⟨0⟩`
    returns `some ptr`, so `evalLocal` returns `some ⟨ptr⟩` whose
    provenance is `some ⟨⟨0⟩⟩`. -/
private theorem evalLocal_initialMachine_provenance
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h)) (pp : PlacePtr)
    (heval : evalLocal (initialMachine pr h) ⟨0⟩ h_R = some pp) :
    pp.ptr.provenance = some ⟨⟨0⟩⟩ := by
  unfold evalLocal currentFrame mapGet at heval
  change ((initialMachine pr h).thread.stack.head!.locals.get? ⟨0⟩).bind
      (fun ptr => some (PlacePtr.mk ptr)) = some pp at heval
  unfold initialMachine Machine.createFrame
    StackFrame.storageLive at heval
  simp only [storageDead_initFrame_mapEmpty, liveAndStoreArgs_nil,
             List.head!] at heval
  unfold mapInsert at heval
  rw [Std.HashMap.get?_insert, beq_self_eq_true] at heval
  simp only [↓reduceIte, Option.bind_some] at heval
  injection heval with hpp
  rw [← hpp]
  -- `Memory.allocate (Memory⟨[]⟩) _`'s `snd` is `AllocId⟨[].length⟩`,
  -- i.e. `AllocId⟨0⟩` by `rfl` after unfolding `allocate`.
  show (some (Provenance.mk
    ((Memory.allocate (Memory.mk []) _).snd))
    : Option Provenance) = some ⟨⟨0⟩⟩
  unfold Memory.allocate
  rfl

/-- Every allocation in the initial machine has data
    `List.replicate _ AbstractByte.uninit`. The initial machine
    performs exactly one `Memory.allocate` call (for `Local⟨0⟩`),
    which constructs an allocation whose `data` is precisely
    `List.replicate sz AbstractByte.uninit`. -/
private theorem initialMachine_alloc_data_eq_replicate
    (pr : Program) (h : validProgram pr) (a : Allocation)
    (ha : a ∈ (initialMachine pr h).mem.allocs) :
    ∃ sz, a.data = List.replicate sz AbstractByte.uninit := by
  unfold initialMachine Machine.createFrame StackFrame.storageLive at ha
  simp only [storageDead_initFrame_mapEmpty, liveAndStoreArgs_nil] at ha
  unfold Memory.allocate at ha
  simp only [List.nil_append] at ha
  rw [List.mem_singleton] at ha
  -- The `IsSized` obligation mirrors the one discharged inside
  -- `storageLive`'s `proof[…]` for `Local⟨0⟩`.
  have hvb := validBody_startProgram pr h
  refine ⟨Ty.sizeOf (Program.startProgram pr h).decls[0]! ?_, ?_⟩
  · show Ty.IsSized ((Program.startProgram pr h).decls[0]!)
    rw [getElem!_pos (Program.startProgram pr h).decls 0
      (List.length_pos_iff.mpr hvb.1)]
    exact hvb.2.2.2.1 _ (List.getElem_mem _)
  · rw [ha]; rfl

private theorem initialMachine_alloc_data_uninit
    (pr : Program) (h : validProgram pr) (idx : Nat)
    (b : AbstractByte)
    (hb : b ∈ ((initialMachine pr h).mem.allocs[idx]!).data) :
    b = AbstractByte.uninit := by
  have hlen : (initialMachine pr h).mem.allocs.length = 1 :=
    mem_initialMachine_length_one pr h
  by_cases h_in : idx < (initialMachine pr h).mem.allocs.length
  · -- In-bounds: `[idx]!` reduces to `[idx]'h_in`, which is in the list.
    have h_pos : (initialMachine pr h).mem.allocs[idx]! =
        (initialMachine pr h).mem.allocs[idx]'h_in :=
      getElem!_pos (initialMachine pr h).mem.allocs idx h_in
    rw [h_pos] at hb
    have hmem : (initialMachine pr h).mem.allocs[idx]'h_in ∈
        (initialMachine pr h).mem.allocs := List.getElem_mem h_in
    obtain ⟨_, hd⟩ := initialMachine_alloc_data_eq_replicate pr h _ hmem
    rw [hd] at hb
    exact List.eq_of_mem_replicate hb
  · -- Out-of-bounds: `[idx]!` returns `default`, whose `.data` is `[]`.
    have h_eq : (initialMachine pr h).mem.allocs[idx]! =
        (default : Allocation) :=
      getElem!_neg (initialMachine pr h).mem.allocs idx h_in
    rw [h_eq] at hb
    have h_def_data : (default : Allocation).data = ([] : List AbstractByte) := rfl
    rw [h_def_data] at hb
    exact (List.not_mem_nil hb).elim

/-- Every byte returned by `Memory.load` on the initial machine is
    `.uninit`. -/
private theorem load_initialMachine_all_uninit
    (pr : Program) (h : validProgram pr) (ptr : ThinPointer) (len : Nat)
    (b : AbstractByte)
    (hb : b ∈ Memory.load (initialMachine pr h).mem ptr len) :
    b = AbstractByte.uninit := by
  rcases hck : Memory.checkPtr (initialMachine pr h).mem ptr len with _ | ⟨aid, offset⟩
  · -- `checkPtr` failed → load returns `[]`.
    have heq : Memory.load (initialMachine pr h).mem ptr len = [] := by
      unfold Memory.load; rw [hck]
    rw [heq] at hb
    exact (List.not_mem_nil hb).elim
  · -- `checkPtr` succeeded → load returns `readBytesAt alloc.data offset len`.
    have heq : Memory.load (initialMachine pr h).mem ptr len =
        Memory.readBytesAt
          ((initialMachine pr h).mem.allocs[aid.index]!).data offset len := by
      unfold Memory.load; rw [hck]
    rw [heq] at hb
    unfold Memory.readBytesAt at hb
    have hsub := List.mem_of_mem_take hb
    have hsub' := List.mem_of_mem_drop hsub
    exact initialMachine_alloc_data_uninit pr h aid.index b hsub'

/-- `decodePtr` returns `none` on any byte sequence drawn from the
    initial machine's memory, since every such byte is `.uninit`
    so the inner `data` call fails. -/
private theorem decodePtr_load_initialMachine
    (pr : Program) (h : validProgram pr) (ptr : ThinPointer) :
    decodePtr (Memory.load (initialMachine pr h).mem ptr 8) =
      (none : Option ThinPointer) := by
  have hbytes := load_initialMachine_all_uninit pr h ptr 8
  generalize hL : Memory.load (initialMachine pr h).mem ptr 8 = bs at hbytes
  cases bs with
  | nil => rfl
  | cons b _ =>
    have hb : b = AbstractByte.uninit := hbytes b List.mem_cons_self
    rw [hb]
    rfl

/-- If `pp.ptr.provenance = some ⟨⟨0⟩⟩` and `evalProjs` succeeds on
    the initial machine starting from `pp`, then the resulting place
    pointer also has provenance `some ⟨⟨0⟩⟩`. The `.field`,
    `.downcast`, and `.index` arms preserve provenance verbatim; the
    `.deref` arm short-circuits because `decodePtr` fails on the
    initial machine's memory (every byte is `.uninit`). -/
private theorem evalProjs_initialMachine_provenance
    (pr : Program) (h : validProgram pr)
    (h_R : Runnable (initialMachine pr h)) :
    ∀ (projs : List ProjElem) (pp : PlacePtr) (ty : Ty)
      (pp' : PlacePtr) (ty' : Ty),
    pp.ptr.provenance = some ⟨⟨0⟩⟩ →
    evalProjs (initialMachine pr h) pp ty projs h_R = some ⟨pp', ty'⟩ →
    pp'.ptr.provenance = some ⟨⟨0⟩⟩ := by
  intro projs
  induction projs with
  | nil =>
    intro pp ty pp' ty' hprov heval
    -- `evalProjs m pp ty [] _ = some ⟨pp, ty⟩`, so `pp = pp'`.
    simp only [evalProjs] at heval
    injection heval with heq
    injection heq with hpp _
    rw [← hpp]
    exact hprov
  | cons e rest ih =>
    intro pp ty pp' ty' hprov heval
    cases e with
    | field idx fty =>
      -- `evalProjs m pp ty (.field idx fty :: rest) = (evalField pp idx ty).bind (...)`
      simp only [evalProjs] at heval
      cases hef : evalField pp idx ty with
      | none => rw [hef] at heval; simp at heval
      | some pair =>
        obtain ⟨fp, ft⟩ := pair
        rw [hef] at heval
        simp only [Option.bind_some] at heval
        -- `fp.ptr.provenance = pp.ptr.provenance` because `evalField`
        -- only adjusts the address. The non-`ctor` arms of `evalField`
        -- never return `some`, so `hef` derives `False`; the `ctor`
        -- arm exposes the new pointer's address but keeps provenance.
        have hfp : fp.ptr.provenance = pp.ptr.provenance := by
          cases ty with
          | bool | int _ | param _ | alias _ _ _ | ref _ _ _ | box _ | array _ _ =>
            simp [evalField] at hef
          | ctor _ args =>
            simp only [evalField] at hef
            cases hofs : fieldOffset args idx.index with
            | none => rw [hofs] at hef; simp at hef
            | some off =>
              rw [hofs] at hef
              simp only [Option.bind_some] at hef
              injection hef with h1
              injection h1 with h1l _
              rw [← h1l]
        exact ih fp ft pp' ty' (hfp ▸ hprov) heval
    | downcast variantIdx =>
      simp only [evalProjs] at heval
      exact ih pp ty pp' ty' hprov heval
    | deref =>
      cases ty with
      | ref _ _ _ | box _ =>
        simp only [evalProjs] at heval
        rw [decodePtr_load_initialMachine pr h pp.ptr] at heval
        simp at heval
      | bool | int _ | param _ | alias _ _ _ | ctor _ _ | array _ _ =>
        all_goals (simp [evalProjs] at heval)
    | index lcl =>
      cases ty with
      | array elem _ =>
        simp only [evalProjs] at heval
        cases hsz : Ty.bytes elem with
        | none => rw [hsz] at heval; simp at heval
        | some elemSz =>
          rw [hsz] at heval
          simp only [Option.bind_some] at heval
          cases hil : evalLocal (initialMachine pr h) lcl h_R with
          | none => rw [hil] at heval; simp at heval
          | some idxPp =>
            rw [hil] at heval
            simp only [Option.bind_some] at heval
            have hbytes := load_initialMachine_all_uninit pr h idxPp.ptr 8
            cases hd : data (Memory.load (initialMachine pr h).mem idxPp.ptr 8) with
            | none => rw [hd] at heval; simp at heval
            | some idxRaw =>
              rw [hd] at heval
              simp only [Option.bind_some] at heval
              -- `data` returned `some idxRaw`; on the initial machine this
              -- forces `idxRaw = []` because the loaded bytes are `[]` or
              -- begin with `.uninit` (the latter making `data` fail).
              have hempty : idxRaw = [] := by
                cases hib : Memory.load (initialMachine pr h).mem idxPp.ptr 8 with
                | nil => rw [hib] at hd; simp [data] at hd; exact hd
                | cons b _ =>
                  rw [hib, hbytes b (hib ▸ List.mem_cons_self)] at hd
                  simp [data] at hd
              -- After substituting `idxRaw = []`, `decodeLeUnsigned [] = 0`,
              -- so the offset added is `0` and the new pointer collapses to
              -- the original `pp` modulo the address. Provenance is
              -- preserved verbatim.
              subst hempty
              -- The new pp has provenance `pp.ptr.provenance`.
              apply ih (PlacePtr.mk
                  (ThinPointer.mk
                    (Address.mk (pp.ptr.addr.addr + decodeLeUnsigned [] * elemSz))
                    pp.ptr.provenance))
                elem pp' ty' hprov heval
      | bool | int _ | param _ | alias _ _ _ | ref _ _ _ | box _ | ctor _ _ =>
        all_goals (simp [evalProjs] at heval)

/-- The provenance of any successful `evalPlace` in
    `initialMachine pr h` is `some ⟨⟨0⟩⟩` — the `AllocId` of the
    unique allocation.

    Proof: `evalPlace` runs `evalLocal` on `p.local`, then walks
    `p.projection` via `evalProjs`. The base pointer comes from the
    locals map; in `initialMachine` the only entry is for
    `Local⟨0⟩` with provenance `some ⟨⟨0⟩⟩` (per the construction
    in `storageLive`). The projection arms (`evalProjs`'s `.field`
    / `.downcast` / `.index` cases) preserve provenance verbatim;
    the `.deref` arm needs `decodePtr` to succeed on memory bytes,
    but `initialMachine` has uninit bytes only, so `decodePtr`
    returns `none` and `evalProjs` short-circuits. -/
private theorem evalPlace_provenance_initialMachine
    (pr : Program) (h : validProgram pr) (p : Place)
    (h_R : Runnable (initialMachine pr h)) (pp : PlacePtr) (ty : Ty)
    (heval : evalPlace (initialMachine pr h) p h_R = some ⟨pp, ty⟩) :
    pp.ptr.provenance = some ⟨⟨0⟩⟩ := by
  unfold evalPlace at heval
  rw [Option.bind_eq_some_iff] at heval
  obtain ⟨rootPp, hL, hev⟩ := heval
  have hlocal := evalLocal_initialMachine_local0 pr h p.local h_R rootPp hL
  rw [hlocal] at hL
  have hroot := evalLocal_initialMachine_provenance pr h h_R rootPp hL
  exact evalProjs_initialMachine_provenance pr h h_R p.projection
    rootPp _ pp ty hroot hev

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
      (PcgData.init (Program.startProgram pr h)) := by
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
  have h_alloc_eq := placeAllocation_of_hasAllocation h_Runnable h_hasAlloc1
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
           (initialMachine pr proof[h_validProgram]) (PcgData.init
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
`p ∈ places (PcgData.init body)` forces `p.projection = []`.

Combined with `hasAllocation_initialMachine` (which forces
`p.local = ⟨0⟩`), the antecedent collapses both `p` and `p'`
to `⟨⟨0⟩, []⟩` — contradicting the `p ≠ p'` antecedent of
`ConnectedInvariant`. -/

/-! ## Helpers for `places_initialPcg_root` -/

-- `LawfulHashable Place` is provided in `MIR/Place.lean`,
-- alongside the `LawfulBEq Place` derive it depends on.

/-- "Forward direction" of `mem_flatMapList_iff`, but stated
    as a forward implication (no `iff`) so we can avoid the
    `EquivBEq` requirement of the `mem_union_iff` lemmas. We
    only ever need this direction for `places_initialPcg_root`,
    and proving it amounts to: every element added to the
    foldl accumulator came from some `f a` for `a ∈ l`. -/
private theorem mem_of_mem_flatMapList {α β : Type}
    [BEq β] [EquivBEq β] [Hashable β] [LawfulHashable β]
    (l : List α) (f : α → Set β) (b : β) :
    b ∈ Set.flatMapList l f → ∃ a ∈ l, b ∈ f a := by
  unfold Set.flatMapList
  suffices ∀ acc : Std.HashSet β,
      b ∈ l.foldl (fun acc x => Std.HashSet.union acc (f x)) acc →
        b ∈ acc ∨ ∃ a ∈ l, b ∈ f a by
    intro h
    rcases this ∅ h with h_empty | h_in
    · exact absurd h_empty (Std.HashSet.not_mem_empty)
    · exact h_in
  intro acc
  induction l generalizing acc with
  | nil => intro h; exact Or.inl h
  | cons x xs ih =>
    rw [List.foldl_cons]
    intro h
    rcases ih _ h with hAcc | ⟨a, ha, hb⟩
    · -- `hAcc : b ∈ acc.union (f x)`. Without lawful
      -- instances we can't fully decompose, but we can
      -- *partially* decompose using `Std.HashSet.contains`
      -- via the `Decidable` instance for membership.
      rw [Std.HashSet.union_eq] at hAcc
      by_cases hAcc' : b ∈ acc
      · exact Or.inl hAcc'
      · exact Or.inr ⟨x, List.mem_cons_self,
          Std.HashSet.mem_of_mem_union_of_not_mem_left hAcc hAcc'⟩
    · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hb⟩

/-- Every `OwnedLocal` produced by `OwnedState.initial body` is
    either `.unallocated` or `.allocated (.leaf _)` — the helper
    never builds an internal init tree. -/
private theorem ownedState_initial_locals_form
    (body : Body) (ol : OwnedLocal) (idx : Nat)
    (h : (ol, idx) ∈ (OwnedState.initial body).locals.zipIdx) :
    ol = .unallocated ∨ ∃ d, ol = .allocated (.leaf d) := by
  rw [List.mk_mem_zipIdx_iff_getElem?] at h
  unfold OwnedState.initial at h
  simp only at h
  -- After unfolding, `(OwnedState.initial body).locals[idx]?`
  -- reduces to `body.decls.zipIdx.map (fun ⟨_, i⟩ => …)[idx]?`,
  -- which (when `idx < body.decls.length`) returns the
  -- if-then-else arm for that index.
  rcases hi : body.decls.zipIdx[idx]? with _ | ⟨ty, k⟩
  · -- Out-of-bounds: the map is also out-of-bounds, so
    -- `…[idx]?` is `none`, contradicting `h`.
    simp [List.getElem?_map, hi] at h
  · -- In-bounds: `h` reduces to `if k == 0 then … else …`.
    simp [List.getElem?_map, hi] at h
    by_cases hk0 : k = 0
    · subst hk0; simp at h; exact Or.inr ⟨_, h.symm⟩
    · simp [hk0] at h
      by_cases hkArg : k ≤ body.numArgs
      · simp [hkArg] at h; exact Or.inr ⟨_, h.symm⟩
      · simp [hkArg] at h; exact Or.inl h.symm

/-- For the initial PCG, `edges` only ever produces `.unpack`
    edges (no `.deref`/`.borrow`/`.borrowFlow`/`.abstraction`):
    the borrows graph is empty and `transientState = none`,
    so the only contributions to `edges` are `localsUnpackEdges`
    wrapped in `PcgEdge.unpack`. -/
private theorem edges_initialPcg_all_unpack
    (body : Body) (e : PcgEdge Place)
    (h : e ∈ edges (PcgData.init body)) :
    ∃ ue, e = .unpack ue := by
  unfold edges PcgData.init at h
  simp only [transientReadPlaces,
             BorrowsGraph.blockedCurrentPlaces] at h
  rcases List.mem_append.mp h with h_unpack | h_bg
  · -- Edge came from `unpackEdges`, which is `.map .unpack`.
    rcases List.mem_map.mp h_unpack with ⟨ue, _, rfl⟩
    exact ⟨ue, rfl⟩
  · -- Edge came from `pd.bg.edges.toList.map …`, but
    -- `mapEmpty.toList = []`, so this case is empty.
    simp [mapEmpty] at h_bg

/-- A place tracked by the initial PCG must be a bare local
    (empty projection): the only places in the initial PCG
    are the roots of each allocated local's `.leaf` init
    tree. -/
theorem places_initialPcg_root
    (body : Body) (p : Place)
    (h_places : p ∈ places (PcgData.init body)) :
    p.projection = [] := by
  -- `places (PcgData.init body) = owned ∪ edgeP`. The initial
  -- PCG's borrows graph is empty and `transientState = none`,
  -- so all edges in `edges (PcgData.init body)` are unpack
  -- edges; the `edgeP` half of `places` matches only `.deref`
  -- and `.borrow`, so `edgeP = ∅`. The `owned` half walks
  -- each allocated local's init tree via `itPlaces`; in
  -- `OwnedState.initial body` every allocated local carries a
  -- `.leaf _` tree, so `itPlaces (.leaf _) base [] =
  -- ⦃Place⟨base, []⟩⦄` — every place there has an empty
  -- projection.
  unfold places at h_places
  -- `places` returns `owned ++ edgeP` where `++` is the
  -- `Append.append` instance backed by `Std.HashSet.union`.
  -- Decompose membership: `p ∈ owned ∨ p ∈ edgeP`. We use
  -- `mem_of_mem_union_of_not_mem_*` so we don't need the
  -- `EquivBEq Place` instance the iff form would require.
  change p ∈ Std.HashSet.union _ _ at h_places
  rw [Std.HashSet.union_eq] at h_places
  by_cases h_owned : p ∈
      (Set.flatMapList ((PcgData.init body).os.locals.zipIdx)
        fun x => match x.fst with
          | OwnedLocal.allocated t => itPlaces t ⟨x.snd⟩ []
          | OwnedLocal.unallocated => ∅)
  case neg =>
    have h_edge :=
      Std.HashSet.mem_of_mem_union_of_not_mem_left h_places h_owned
    -- Edge side: `edgeP` only emits places for `.deref` and
    -- `.borrow` edges; `edges_initialPcg_all_unpack` rules
    -- those out.
    rcases mem_of_mem_flatMapList _ _ _ h_edge with
      ⟨e, h_eIn, h_pIn⟩
    rcases edges_initialPcg_all_unpack body e h_eIn with
      ⟨ue, rfl⟩
    -- The match-arm for `.unpack` returns `∅`; nothing in it.
    simp at h_pIn
  case pos =>
    -- Owned side: walk into the per-local init tree.
    rcases mem_of_mem_flatMapList _ _ _ h_owned
      with ⟨⟨ol, idx⟩, h_mem, h_pIn⟩
    -- `ownedState_initial_locals_form` classifies `ol`.
    rcases ownedState_initial_locals_form body ol idx h_mem with
      hol | ⟨d, hol⟩
    · subst hol
      -- `.unallocated` contributes `∅`; nothing is in there.
      simp at h_pIn
    · subst hol
      -- `.allocated (.leaf d)` contributes
      -- `itPlaces (.leaf d) ⟨idx⟩ [] = Set.singleton ⟨⟨idx⟩, []⟩`.
      -- The singleton's only element is `⟨⟨idx⟩, []⟩`. The
      -- `mem_insert` decomposition gives a `BEq` witness; we
      -- unfold `Place`'s structural `BEq` directly to extract
      -- `p.projection = []` without going through a generic
      -- `LawfulBEq Place` instance.
      simp only [itPlaces, Set.singleton] at h_pIn
      rcases Std.HashSet.mem_insert.mp h_pIn with hbeq | hempty
      · cases p with
        | mk pLocal pProj =>
          simp [BEq.beq, instBEqPlace.beq] at hbeq
          obtain ⟨_, hp⟩ := hbeq
          -- `hp : ([] : List ProjElem) == pProj`. Decide on
          -- `pProj` and either get `pProj = []` or a
          -- contradiction.
          cases pProj with
          | nil => rfl
          | cons _ _ => simp [List.beq] at hp
      · exact absurd hempty Std.HashSet.not_mem_empty

/-- **Singleton lemma**: under the antecedents of
    `ConnectedInvariant` for the initial machine, the set of
    places `p` that satisfy `p ∈ places (PcgData.init ..)` *and*
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
      places (PcgData.init (Program.startProgram pr h)))
    (h_alloc : Machine.placeAllocation
      (initialMachine pr h) p h_R = some a) :
    p = ⟨⟨0⟩, []⟩ := by
  obtain ⟨loc, projs⟩ := p
  have h_proj := places_initialPcg_root (Program.startProgram pr h) ⟨loc, projs⟩ h_places
  have h_local := placeAllocation_initialMachine_local0 pr h ⟨loc, projs⟩ a h_R h_alloc
  cases h_proj; cases h_local; rfl

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
      (PcgData.init (Program.startProgram pr h)) := by
  intro p p' a a' h_distinct h_Runnable _h_validPlace _h_validPlace'
        h_places h_places' h_alloc_p h_alloc_p'
  exfalso
  -- Extract the underlying `Machine.placeAllocation` equations.
  have h_alloc_eq_p := placeAllocation_of_hasAllocation h_Runnable h_alloc_p
  have h_alloc_eq_p' := placeAllocation_of_hasAllocation h_Runnable h_alloc_p'
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
           (initialMachine pr proof[h_validProgram]) (PcgData.init
              (Program.startProgram
                 pr proof[h_validProgram]))
  proof connectedInvariant_initialMachine

end Properties
