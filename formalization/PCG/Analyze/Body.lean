import Core.Dsl.DefFn
import Core.Dsl.DefRaw
import MIR.Body
import PCG.Analyze.AnalysisResults
import PCG.Analyze.AnalysisState
import PCG.Analyze.PcgData
import PCG.PcgData
import PCG.PcgDomainData

-- ══════════════════════════════════════════════
-- Successors of a terminator
-- ══════════════════════════════════════════════

defFn termSuccessors (.plain "termSuccessors")
  (doc! "List the basic-block successors of a terminator. \
    `goto`, `drop`, and `call` each have a single successor; \
    `switchInt` lists every block referenced by its `cases` \
    map together with its `fallback`; `return` and \
    `unreachable` have none.")
  (t "The terminator." : Terminator)
  : List BasicBlockIdx where
  | .goto target => [target]
  | .switchInt _ cases fallback =>
      (cases·map fun ⟨_, bb⟩ => bb) ++ [fallback]
  | .return_ => []
  | .unreachable => []
  | .drop _ target => [target]
  | .call _ _ _ next => [next]

-- ══════════════════════════════════════════════
-- BasicBlockIdx list membership
-- ══════════════════════════════════════════════

defFn bbContains (.plain "bbContains")
  (doc! "Whether a basic-block index appears in a list, \
    compared by `index`.")
  (xs "The list to search." : List BasicBlockIdx)
  (b "The block index to look for." : BasicBlockIdx)
  : Bool where
  | [] ; _ => false
  | x :: rest ; b =>
      if x↦index == b↦index then true
      else bbContains rest b

-- ══════════════════════════════════════════════
-- DFS helpers — `dfsVisit`'s `visited` list grows
-- monotonically, so structural recursion alone can't see
-- termination; the `partial` modifier sidesteps the check.
-- The DSL has no `partial def` surface syntax, so the
-- helper is spelled as a `defRaw` block: the same source
-- string is elaborated here and emitted into the generated
-- Lean project. The successor list is inlined (rather than
-- routed through `termSuccessors`) because the export
-- splices this block into the `middle` slot, ahead of the
-- DSL-generated function definitions.
-- ══════════════════════════════════════════════

defRaw middle => {
/-- DFS-postorder walk of the CFG rooted at `curr`. The
    successor list is inlined to avoid a forward reference
    to `Terminator.termSuccessors`, which is generated
    below this `middle` extra. -/
private partial def dfsVisit
    (body : Body)
    (visited : List BasicBlockIdx)
    (post : List BasicBlockIdx)
    (curr : BasicBlockIdx)
    : List BasicBlockIdx × List BasicBlockIdx :=
  if visited.any (·.index == curr.index) then
    (visited, post)
  else
    let visited1 := curr :: visited
    let block := body.blocks[curr.index]!
    let succs : List BasicBlockIdx :=
      match block.terminator with
      | .goto target => [target]
      | .switchInt _ cases fallback =>
          cases.map (·.2) ++ [fallback]
      | .return_ => []
      | .unreachable => []
      | .drop _ target => [target]
      | .call _ _ _ next => [next]
    let r := succs.foldl
      (fun acc s => dfsVisit body acc.1 acc.2 s)
      (visited1, post)
    (r.1, r.2 ++ [curr])

/-- Reverse postorder of the CFG starting from block 0. -/
private def reversePostorder (body : Body)
    : List BasicBlockIdx :=
  (dfsVisit body [] [] ⟨0⟩).2.reverse
}

-- ══════════════════════════════════════════════
-- Pushing a block's exit state to its successors
-- ══════════════════════════════════════════════

-- `pushOneNewEntry` uses `match heq : mapGet … with` to
-- bind the lookup equation as a hypothesis; the proof of
-- `PcgData.join`'s length precondition projects the caller's
-- `forAll`-over-`mapValues` invariant down to the looked-up
-- value via `mem_mapValues_of_mapGet_eq_some heq`. The DSL's
-- `match h : scrut with` form (added in this PR) drops to
-- this same Lean code.
--
-- The export's namespace inference puts this function in
-- `namespace AnalysisState` (its first parameter is an
-- `AnalysisState`); we wrap the source-side declaration in
-- the same namespace so the `defRaw inFns` blocks below can
-- reference it via the same fully-qualified name in both
-- builds.
namespace AnalysisState
defFn pushOneNewEntry (.plain "pushOneNewEntry")
  (doc! "Compute the new pending entry for `succ`. If there \
    is already a pending entry, join it with the \
    predecessor's exit state via `PcgData.join`; otherwise \
    rebase `exit` to `succ` and return that.")
  (state "The current analysis state." : AnalysisState)
  (exit "The exit state of the just-processed predecessor."
      : PcgData Place)
  (succ "The successor block to push into."
      : BasicBlockIdx)
  requires mapValues state↦entryStates·forAll fun e =>
             e↦os↦locals·length = exit↦os↦locals·length
  : PcgData Place :=
    match heq : mapGet state↦entryStates succ with
    | .some existing =>
        PcgData.join
          existing exit succ
          proof[h_pre0 existing
            (mem_mapValues_of_mapGet_eq_some heq)]
    | .none =>
        PcgData⟨exit↦bg, exit↦os, succ, None⟩
    end
end AnalysisState

-- `pushOne`, the preservation lemma, and `pushToSuccessors`
-- below are kept in raw Lean rather than `defFn` so the
-- recursive call inside `pushToSuccessors` can apply
-- `pushOne_preserves_lengths` explicitly — the DSL's
-- auto-discharged precondition tactic can't bridge
-- `state.entryStates` to `(pushOne …).entryStates`. They are
-- registered with `defRaw inFns` so they appear *after* the
-- `defFn pushOneNewEntry` declaration (which they
-- reference) when the export interleaves raw blocks with
-- DSL-generated function definitions in source order.
defRaw inFns => {
/-- Join an exit state `exit` into the pending entry state of
    one successor block. If `succ` already has a pending entry,
    the two are combined with `PcgData.join`; otherwise the
    contribution becomes the entry, rebased to `succ`. The
    precondition asserts that every PCG already pending in
    `state.entryStates` shares its `os.locals` length with the
    exit PCG — exactly what `PcgData.join` needs in the
    `.some existing` branch of `pushOneNewEntry`. -/
private def AnalysisState.pushOne (state : AnalysisState)
    (exit : PcgData Place) (succ : BasicBlockIdx)
    (h_pre0 : ∀ e ∈ mapValues state.entryStates,
                e.os.locals.length = exit.os.locals.length)
    : AnalysisState :=
  let newEntry :=
    AnalysisState.pushOneNewEntry state exit succ h_pre0
  let entries1 :=
    mapInsert state.entryStates succ newEntry
  { state with entryStates := entries1 }

-- Preservation lemma used at the recursive call inside
-- `pushToSuccessors`: applying `pushOne` keeps the
-- shared-locals-length invariant. The proof factors through
-- two helpers — `ownedLocalsMeet_length` (its result list has
-- the input length) and `pushOneNewEntry_length` (the new
-- entry inherits `exit.os.locals.length`) — and reduces the
-- map step to `mem_mapValues_mapInsert` plus the caller's
-- existing hypothesis.
private theorem ownedLocalsMeet_length
    (xs ys : List OwnedLocal) (h : xs.length = ys.length) :
    (ownedLocalsMeet xs ys h).length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hh : xs.length = ys.length := by simpa using h
          have heq := ih ys hh
          cases x with
          | allocated ix =>
              cases y with
              | allocated iy =>
                  show (OwnedLocal.allocated _ ::
                          ownedLocalsMeet xs ys hh).length =
                       xs.length + 1
                  simp [List.length_cons, heq]
              | unallocated =>
                  show (OwnedLocal.unallocated ::
                          ownedLocalsMeet xs ys hh).length =
                       xs.length + 1
                  simp [List.length_cons, heq]
          | unallocated =>
              cases y with
              | allocated _ =>
                  show (OwnedLocal.unallocated ::
                          ownedLocalsMeet xs ys hh).length =
                       xs.length + 1
                  simp [List.length_cons, heq]
              | unallocated =>
                  show (OwnedLocal.unallocated ::
                          ownedLocalsMeet xs ys hh).length =
                       xs.length + 1
                  simp [List.length_cons, heq]

private theorem AnalysisState.pushOneNewEntry_length
    (state : AnalysisState) (exit : PcgData Place)
    (succ : BasicBlockIdx)
    (h : ∀ e ∈ mapValues state.entryStates,
          e.os.locals.length = exit.os.locals.length) :
    (AnalysisState.pushOneNewEntry
      state exit succ h).os.locals.length =
      exit.os.locals.length := by
  unfold AnalysisState.pushOneNewEntry
  split
  · rename_i existing heq
    simp only [PcgData.join, OwnedState.meet,
      ownedLocalsMeet_length]
    exact h existing
      (mem_mapValues_of_mapGet_eq_some heq)
  · rfl

private theorem AnalysisState.pushOne_preserves_lengths
    (state : AnalysisState) (exit : PcgData Place)
    (succ : BasicBlockIdx)
    (h : ∀ e ∈ mapValues state.entryStates,
          e.os.locals.length = exit.os.locals.length) :
    ∀ e ∈ mapValues
            (AnalysisState.pushOne
              state exit succ h).entryStates,
      e.os.locals.length = exit.os.locals.length := by
  intro e he
  unfold AnalysisState.pushOne at he
  simp only at he
  rcases mem_mapValues_mapInsert he with rfl | hold
  · exact AnalysisState.pushOneNewEntry_length
      state exit succ h
  · exact h e hold
}

defFn pushToSuccessors (.plain "pushToSuccessors")
  (doc! "Fold an exit state into every successor's pending \
    entry state via `pushOne`.")
  (state "The current analysis state." : AnalysisState)
  (exit "The exit state of the just-processed predecessor."
      : PcgData Place)
  (succs "Successor blocks of the predecessor."
      : List BasicBlockIdx)
  -- Same shared-locals-length invariant pushOne needs:
  -- propagated unchanged into each `pushOne` call. The
  -- recursive call's auto-discharge needs the `pushOne`
  -- preservation lemma — supplied via the `using […]` clause
  -- below, which splices the lemma name into the
  -- `simp_all […]` tactic the Lean export emits at recursive
  -- call sites.
  requires mapValues state↦entryStates·forAll fun e =>
             e↦os↦locals·length = exit↦os↦locals·length
    using [AnalysisState.pushOne_preserves_lengths]
  : AnalysisState where
  | state ; _ ; [] => state
  | state ; exit ; s :: rest =>
      pushToSuccessors
        (AnalysisState.pushOne state exit s proof[h_pre0])
        exit rest

-- ══════════════════════════════════════════════
-- Forward step: process one block, propagate to successors
-- ══════════════════════════════════════════════

-- The discharge of `pushToSuccessors`'s shared-locals-length
-- precondition collapses through `validAnalysisState body
-- state` plus a body-tied exit-validity hypothesis: both
-- sides of the equation `e.os.locals.length =
-- exit.os.locals.length` reduce to `body.decls.length`, so
-- the equation collapses to `rfl`. The exit-validity
-- hypothesis is established by tracing length preservation
-- through `obtain → obtainTriples → analyze → analyzeAt →
-- analyzeStmtsFrom → analyzeBlock`: each step in the chain
-- only mutates `pd.os.locals` via `setOwnedLocalAt`, which
-- maps over `os.locals.zipIdx` and so preserves length.
defRaw inFns => {
-- `setOwnedLocalAt`/`obtainWriteOwned` are top-level in source
-- but lifted into `OwnedState`/`OwnedState` respectively in
-- the generated module (their first param is `OwnedState`).
-- `open OwnedState` resolves the unqualified references in the
-- generated build; in source they're already top-level so the
-- open is a no-op there.
open OwnedState

/-- `setOwnedLocalAt` preserves `os.locals.length`: the
    function maps `f` over `os.locals.zipIdx`, and
    `(xs.zipIdx.map f).length = xs.length`. -/
private theorem setOwnedLocalAt_locals_length
    (os : OwnedState) (idx : Nat) (newOl : OwnedLocal) :
    (setOwnedLocalAt os idx newOl).locals.length =
      os.locals.length := by
  unfold setOwnedLocalAt
  simp [List.length_map, List.length_zipIdx]

/-- `obtainWriteOwned` either fails or produces a new
    `OwnedState` with the same `locals.length`: every `Some`-arm
    routes through `setOwnedLocalAt`, which preserves length. -/
private theorem obtainWriteOwned_locals_length
    {os : OwnedState} {p : Place} {os' : OwnedState}
    (h : obtainWriteOwned os p = some os') :
    os'.locals.length = os.locals.length := by
  unfold obtainWriteOwned at h
  simp only at h
  cases hOl : os.locals[p.local.index]? with
  | none => rw [hOl] at h; simp at h
  | some ol =>
    rw [hOl] at h
    simp only [Option.bind_some] at h
    cases ol with
    | unallocated => simp at h
    | allocated it =>
      simp only at h
      cases hT : obtainWriteInTree it p.projection with
      | none => rw [hT] at h; simp at h
      | some newIt =>
        rw [hT] at h
        simp only [Option.bind_some] at h
        injection h with h_eq
        rw [← h_eq]
        exact setOwnedLocalAt_locals_length os _ _

/-- `PcgData.obtain` preserves `validPcgData`. The four arms of
    its match all leave `os.locals.length` unchanged: the
    `.write` owned arm routes through
    `obtainWriteOwned_locals_length`; the `.write` borrowed and
    `.read` arms only update `transientState`; the catch-all
    returns `None` so the equation is vacuous. -/
private theorem PcgData.obtain_preserves_validPcgData
    {pd : PcgData Place} {body : Body} {p : Place} {c : Capability}
    {h_validPlace : validPlace body p}
    {pd' : PcgData Place}
    (h : PcgData.obtain pd body p c h_validPlace = some pd')
    (hv : validPcgData body pd) :
    validPcgData body pd' := by
  unfold validPcgData at hv ⊢
  unfold PcgData.obtain at h
  cases c with
  | none => simp at h
  | exclusive => simp at h
  | shallowExclusive => simp at h
  | write =>
    simp only at h
    split at h
    · -- owned: `obtainWriteOwned`
      cases hOs : obtainWriteOwned pd.os p with
      | none => rw [hOs] at h; simp at h
      | some newOs =>
        rw [hOs] at h
        simp only [Option.bind_some] at h
        injection h with h_eq
        rw [← h_eq]; simp only
        rw [obtainWriteOwned_locals_length hOs]
        exact hv
    · -- borrowed: only `transientState` updated
      injection h with h_eq
      rw [← h_eq]; simp only; exact hv
  | read =>
    simp only at h
    cases hT : pd.transientState with
    | none =>
      rw [hT] at h
      simp only at h
      injection h with h_eq
      rw [← h_eq]; simp only; exact hv
    | some t =>
      rw [hT] at h
      cases t with
      | readPlaces s =>
        simp only at h
        injection h with h_eq
        rw [← h_eq]; simp only; exact hv
      | writeBorrowedPlace _ => simp at h

/-- `PcgData.obtainTriples` preserves `validPcgData`. By
    induction on the triples list: each step is one
    `PcgData.obtain` call, which preserves `validPcgData`. -/
private theorem PcgData.obtainTriples_preserves_validPcgData
    (body : Body) :
    ∀ {pd : PcgData Place} {triples : List PlaceTriple}
      (h_pre0 : ∀ t ∈ triples, validPlace body t.place)
      {pd' : PcgData Place},
      PcgData.obtainTriples pd body triples h_pre0 = some pd' →
      validPcgData body pd → validPcgData body pd'
  | pd, [], _, pd', h, hv => by
      unfold PcgData.obtainTriples at h
      simp at h; rw [← h]; exact hv
  | pd, t :: rest, h_pre0, pd', h, hv => by
      unfold PcgData.obtainTriples at h
      cases h1 : PcgData.obtain pd body t.place t.pre _ with
      | none => rw [h1] at h; simp at h
      | some pd1 =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        have hv1 :=
          PcgData.obtain_preserves_validPcgData h1 hv
        exact PcgData.obtainTriples_preserves_validPcgData
          body (pd := pd1) (triples := rest) _ h hv1

/-- `PcgData.analyze` preserves `validPcgData`. Unfolds to a
    single `PcgData.obtainTriples` call. -/
private theorem PcgData.analyze_preserves_validPcgData
    {pd : PcgData Place} {body : Body} {loc : Location}
    {phase : EvalStmtPhase} (h_validBody : validBody body)
    {pd' : PcgData Place}
    (h : PcgData.analyze pd body loc phase h_validBody = some pd')
    (hv : validPcgData body pd) :
    validPcgData body pd' := by
  unfold PcgData.analyze at h
  exact PcgData.obtainTriples_preserves_validPcgData body _ h hv

/-- `PcgData.analyzeAt`'s output is `validPcgDomainData`: each
    of its five conjuncts (entryState + four phase outputs) is a
    `validPcgData body` value. The four phases chain through
    `PcgData.analyze`, which preserves `validPcgData`. -/
private theorem PcgData.analyzeAt_validPcgDomainData
    {pd : PcgData Place} {body : Body} {loc : Location}
    (h_validBody : validBody body)
    {dd : PcgDomainData}
    (h : PcgData.analyzeAt pd body loc h_validBody = some dd)
    (hv : validPcgData body pd) :
    validPcgDomainData body dd := by
  unfold PcgData.analyzeAt at h
  cases h1 : PcgData.analyze pd body loc .preOperands h_validBody with
  | none => rw [h1] at h; simp at h
  | some preOp =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    cases h2 : PcgData.analyze preOp body loc .postOperands h_validBody with
    | none => rw [h2] at h; simp at h
    | some postOp =>
      rw [h2] at h
      simp only [Option.bind_some] at h
      cases h3 : PcgData.analyze postOp body loc .preMain h_validBody with
      | none => rw [h3] at h; simp at h
      | some preM =>
        rw [h3] at h
        simp only [Option.bind_some] at h
        cases h4 : PcgData.analyze preM body loc .postMain h_validBody with
        | none => rw [h4] at h; simp at h
        | some postM =>
          rw [h4] at h
          simp only [Option.bind_some] at h
          injection h with h_eq
          rw [← h_eq]
          have hv1 :=
            PcgData.analyze_preserves_validPcgData h_validBody h1 hv
          have hv2 :=
            PcgData.analyze_preserves_validPcgData h_validBody h2 hv1
          have hv3 :=
            PcgData.analyze_preserves_validPcgData h_validBody h3 hv2
          have hv4 :=
            PcgData.analyze_preserves_validPcgData h_validBody h4 hv3
          unfold validPcgDomainData
          exact ⟨hv, hv1, hv2, hv3, hv4⟩

/-- `PcgData.analyzeAt`'s `postMain` is valid (corollary of
    `analyzeAt_validPcgDomainData`'s last conjunct). -/
private theorem PcgData.analyzeAt_postMain_validPcgData
    {pd : PcgData Place} {body : Body} {loc : Location}
    (h_validBody : validBody body)
    {dd : PcgDomainData}
    (h : PcgData.analyzeAt pd body loc h_validBody = some dd)
    (hv : validPcgData body pd) :
    validPcgData body dd.states.postMain :=
  (PcgData.analyzeAt_validPcgDomainData h_validBody h hv).2.2.2.2

/-- `PcgData.analyzeStmtsFrom`'s last element's `postMain` is
    valid when the input PCG is valid. By induction on the
    `remaining` statement list: each step's `analyzeAt`
    preserves validity through `postMain`, and the recursive
    call inherits the chain. -/
private theorem PcgData.analyzeStmtsFrom_last_postMain_validPcgData
    (body : Body) (bb : BasicBlockIdx)
    (h_validBody : validBody body) :
    ∀ {pd : PcgData Place} {idx : Nat}
      {remaining : List Statement} {result : List PcgDomainData},
      PcgData.analyzeStmtsFrom pd body bb idx remaining
          h_validBody = some result →
      validPcgData body pd →
      ∀ last ∈ result.getLast?,
        validPcgData body last.states.postMain
  | pd, idx, [], result, h, hv, last, h_last => by
      unfold PcgData.analyzeStmtsFrom at h
      cases h1 : PcgData.analyzeAt pd body ⟨bb, idx⟩
        h_validBody with
      | none => rw [h1] at h; simp at h
      | some dd =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        injection h with h_eq
        rw [← h_eq] at h_last
        simp [List.getLast?] at h_last
        rw [← h_last]
        exact PcgData.analyzeAt_postMain_validPcgData
          h_validBody h1 hv
  | pd, idx, _ :: rest, result, h, hv, last, h_last => by
      unfold PcgData.analyzeStmtsFrom at h
      cases h1 : PcgData.analyzeAt pd body ⟨bb, idx⟩
        h_validBody with
      | none => rw [h1] at h; simp at h
      | some dd =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        cases h2 : PcgData.analyzeStmtsFrom
          dd.states.postMain body bb (idx + 1) rest h_validBody with
        | none => rw [h2] at h; simp at h
        | some restDDs =>
          rw [h2] at h
          simp only [Option.bind_some] at h
          injection h with h_eq
          rw [← h_eq] at h_last
          have hv1 :=
            PcgData.analyzeAt_postMain_validPcgData
              h_validBody h1 hv
          have h_ind :=
            PcgData.analyzeStmtsFrom_last_postMain_validPcgData
              body bb h_validBody (pd := dd.states.postMain)
              (idx := idx + 1) (remaining := rest)
              (result := restDDs) h2 hv1
          -- `analyzeStmtsFrom` always returns a non-empty list:
          -- both arms of its match produce `Some (… :: …)` or
          -- `Some [_]`. So `restDDs ≠ []`, and
          -- `(dd :: restDDs).getLast? = restDDs.getLast?`.
          have h_restDDs_nonempty : restDDs ≠ [] := by
            intro h_nil
            rw [h_nil] at h2
            -- analyzeStmtsFrom on rest returning Some [] is
            -- impossible: every arm wraps the result in a cons.
            cases rest with
            | nil =>
              unfold PcgData.analyzeStmtsFrom at h2
              cases h2' : PcgData.analyzeAt dd.states.postMain body
                  ⟨bb, idx + 1⟩ h_validBody with
              | none => rw [h2'] at h2; simp at h2
              | some _ => rw [h2'] at h2; simp at h2
            | cons _ _ =>
              unfold PcgData.analyzeStmtsFrom at h2
              cases h2' : PcgData.analyzeAt dd.states.postMain body
                  ⟨bb, idx + 1⟩ h_validBody with
              | none => rw [h2'] at h2; simp at h2
              | some dd' =>
                rw [h2'] at h2
                simp only [Option.bind_some] at h2
                cases h2'' : PcgData.analyzeStmtsFrom
                  dd'.states.postMain body bb (idx + 2) _
                  h_validBody with
                | none => rw [h2''] at h2; simp at h2
                | some _ => rw [h2''] at h2; simp at h2
          rw [List.getLast?_cons_of_ne_nil h_restDDs_nonempty]
            at h_last
          exact h_ind last h_last

/-- `PcgData.analyzeBlock`'s last element's `postMain` is valid
    when the input PCG is valid. Delegates to
    `analyzeStmtsFrom_last_postMain_validPcgData`. -/
private theorem PcgData.analyzeBlock_last_postMain_validPcgData
    {pd : PcgData Place} {body : Body} {bb : BasicBlockIdx}
    (h_validBody : validBody body)
    {result : List PcgDomainData}
    (h : PcgData.analyzeBlock pd body bb h_validBody = some result)
    (hv : validPcgData body pd) :
    ∀ last ∈ result.getLast?,
      validPcgData body last.states.postMain := by
  unfold PcgData.analyzeBlock at h
  exact PcgData.analyzeStmtsFrom_last_postMain_validPcgData
    body bb h_validBody h hv

/-- Every `PcgDomainData` in `analyzeStmtsFrom`'s result list is
    `validPcgDomainData`. Induction on `remaining`: each step's
    `analyzeAt` produces a valid `PcgDomainData` (by
    `analyzeAt_validPcgDomainData`), and the recursive call
    inherits validity. -/
private theorem PcgData.analyzeStmtsFrom_all_validPcgDomainData
    (body : Body) (bb : BasicBlockIdx)
    (h_validBody : validBody body) :
    ∀ {pd : PcgData Place} {idx : Nat}
      {remaining : List Statement} {result : List PcgDomainData},
      PcgData.analyzeStmtsFrom pd body bb idx remaining
          h_validBody = some result →
      validPcgData body pd →
      ∀ dd ∈ result, validPcgDomainData body dd
  | pd, idx, [], result, h, hv, dd, h_dd => by
      unfold PcgData.analyzeStmtsFrom at h
      cases h1 : PcgData.analyzeAt pd body ⟨bb, idx⟩
        h_validBody with
      | none => rw [h1] at h; simp at h
      | some dd' =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        injection h with h_eq
        rw [← h_eq] at h_dd
        rcases List.mem_singleton.mp h_dd with rfl
        exact PcgData.analyzeAt_validPcgDomainData
          h_validBody h1 hv
  | pd, idx, _ :: rest, result, h, hv, dd, h_dd => by
      unfold PcgData.analyzeStmtsFrom at h
      cases h1 : PcgData.analyzeAt pd body ⟨bb, idx⟩
        h_validBody with
      | none => rw [h1] at h; simp at h
      | some dd' =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        cases h2 : PcgData.analyzeStmtsFrom
          dd'.states.postMain body bb (idx + 1) rest h_validBody with
        | none => rw [h2] at h; simp at h
        | some restDDs =>
          rw [h2] at h
          simp only [Option.bind_some] at h
          injection h with h_eq
          rw [← h_eq] at h_dd
          rcases List.mem_cons.mp h_dd with rfl | h_in_rest
          · exact PcgData.analyzeAt_validPcgDomainData
              h_validBody h1 hv
          · have hv1 :=
              PcgData.analyzeAt_postMain_validPcgData
                h_validBody h1 hv
            exact PcgData.analyzeStmtsFrom_all_validPcgDomainData
              body bb h_validBody (pd := dd'.states.postMain)
              (idx := idx + 1) (remaining := rest)
              (result := restDDs) h2 hv1 dd h_in_rest

/-- Every `PcgDomainData` in `analyzeBlock`'s result list is
    `validPcgDomainData`. Delegates to
    `analyzeStmtsFrom_all_validPcgDomainData`. -/
private theorem PcgData.analyzeBlock_all_validPcgDomainData
    {pd : PcgData Place} {body : Body} {bb : BasicBlockIdx}
    (h_validBody : validBody body)
    {result : List PcgDomainData}
    (h : PcgData.analyzeBlock pd body bb h_validBody = some result)
    (hv : validPcgData body pd) :
    ∀ dd ∈ result, validPcgDomainData body dd := by
  unfold PcgData.analyzeBlock at h
  exact PcgData.analyzeStmtsFrom_all_validPcgDomainData
    body bb h_validBody h hv

/-- The exit-state validity replaces the previous axiom.
    `exit` is the `postMain` of the last `PcgDomainData` in
    `analyzeBlock`'s result, with `entry` as the fallback when
    the result list is empty (which never happens in practice
    since `analyzeStmtsFrom` always returns a non-empty list,
    but the fallback keeps the proof structural). The proof
    routes through
    `analyzeBlock_last_postMain_validPcgData` for the
    common case and `h_validAnalysisState.2` for the fallback. -/
theorem computeEntry_exit_validPcgData
    (body : Body) (state : AnalysisState) (bb : BasicBlockIdx)
    (h_validBody : validBody body)
    (h_validAnalysisState : validAnalysisState body state)
    (entry : PcgData Place)
    (h_entry_mem : entry ∈ mapValues state.entryStates)
    (result : List PcgDomainData)
    (h_result : PcgData.analyzeBlock entry body bb h_validBody
                  = some result) :
    validPcgData body
      (match result.getLast? with
       | .some last => last.states.postMain
       | .none => entry) := by
  have h_entry_valid : validPcgData body entry :=
    h_validAnalysisState.2 entry h_entry_mem
  cases h_last : result.getLast? with
  | none => exact h_entry_valid
  | some last =>
    exact PcgData.analyzeBlock_last_postMain_validPcgData
      h_validBody h_result h_entry_valid last h_last

private theorem computeEntry_pushToSuccessors_precond
    (body : Body) (state : AnalysisState)
    (exit : PcgData Place)
    (h_validAnalysisState : validAnalysisState body state)
    (h_exit : validPcgData body exit) :
    ∀ e ∈ mapValues state.entryStates,
      e.os.locals.length = exit.os.locals.length := by
  intro e he
  have h_e : validPcgData body e :=
    h_validAnalysisState.2 e he
  -- Both equations unfold to `body.decls.length`.
  exact h_e.trans h_exit.symm

/-- `AnalysisState.pushOneNewEntry` produces a `validPcgData
    body` value when both `state` and `exit` are valid: in the
    `.some existing` arm, `PcgData.join` preserves
    `validPcgData` (its `os` is `OwnedState.meet`, whose length
    equals the inputs' shared length); in the `.none` arm, the
    new entry inherits `exit.os` directly. -/
private theorem AnalysisState.pushOneNewEntry_validPcgData
    (body : Body) (state : AnalysisState) (exit : PcgData Place)
    (succ : BasicBlockIdx)
    (h_pre0 : ∀ e ∈ mapValues state.entryStates,
                e.os.locals.length = exit.os.locals.length)
    (hve : validPcgData body exit) :
    validPcgData body
      (AnalysisState.pushOneNewEntry state exit succ h_pre0) := by
  unfold validPcgData
  rw [AnalysisState.pushOneNewEntry_length state exit succ h_pre0]
  exact hve

/-- `AnalysisState.pushOne` preserves `validAnalysisState`. The
    `.results` map is unchanged (so `validAnalysisResults`
    transfers); the `.entryStates` map gains/refreshes one entry
    via `mapInsert`, with the new value `validPcgData body` by
    `pushOneNewEntry_validPcgData`. -/
private theorem AnalysisState.pushOne_preserves_validAnalysisState
    (body : Body) (state : AnalysisState) (exit : PcgData Place)
    (succ : BasicBlockIdx)
    (h_pre0 : ∀ e ∈ mapValues state.entryStates,
                e.os.locals.length = exit.os.locals.length)
    (hva : validAnalysisState body state)
    (hve : validPcgData body exit) :
    validAnalysisState body
      (AnalysisState.pushOne state exit succ h_pre0) := by
  refine ⟨?_, ?_⟩
  · -- `validAnalysisResults`: pushOne doesn't touch results.
    unfold AnalysisState.pushOne; simp only
    exact hva.1
  · -- All entryStates values valid.
    unfold AnalysisState.pushOne
    simp only
    intro pcg hpcg
    rcases mem_mapValues_mapInsert hpcg with rfl | hold
    · exact AnalysisState.pushOneNewEntry_validPcgData
        body state exit succ h_pre0 hve
    · exact hva.2 pcg hold

/-- `pushToSuccessors` preserves `validAnalysisState`: induction
    on the successor list, with each step delegating to
    `pushOne_preserves_validAnalysisState`. -/
private theorem pushToSuccessors_preserves_validAnalysisState
    (body : Body) :
    ∀ (state : AnalysisState) (exit : PcgData Place)
      (succs : List BasicBlockIdx)
      (h_pre0 : ∀ e ∈ mapValues state.entryStates,
                  e.os.locals.length = exit.os.locals.length),
      validAnalysisState body state →
      validPcgData body exit →
      validAnalysisState body
        (pushToSuccessors state exit succs h_pre0)
  | state, _, [], _, hva, _ => by
      unfold pushToSuccessors; exact hva
  | state, exit, s :: rest, h_pre0, hva, hve => by
      unfold pushToSuccessors
      have hva' :=
        AnalysisState.pushOne_preserves_validAnalysisState
          body state exit s h_pre0 hva hve
      have h_pre0' :
          ∀ e ∈ mapValues
                  (AnalysisState.pushOne state exit s h_pre0).entryStates,
            e.os.locals.length = exit.os.locals.length :=
        AnalysisState.pushOne_preserves_lengths state exit s h_pre0
      exact pushToSuccessors_preserves_validAnalysisState body
        (AnalysisState.pushOne state exit s h_pre0) exit rest h_pre0'
        hva' hve

/-- `validAnalysisState` is preserved under `mapInsert` of the
    `results` field with a new per-block entry whose elements
    are all `validPcgDomainData`. The `entryStates` field is
    untouched, so its half of the conjunct passes through. The
    `results` half splits a value of `mapValues (mapInsert …)`
    into the inserted list (handled by the per-element validity
    hypothesis) or a value already in the original map (handled
    by the original `validAnalysisResults`). -/
private theorem updateResults_preserves_validAnalysisState
    (body : Body) (state : AnalysisState) (bb : BasicBlockIdx)
    (result : List PcgDomainData)
    (hva : validAnalysisState body state)
    (hres : ∀ pdd ∈ result, validPcgDomainData body pdd) :
    validAnalysisState body
      { state with results := mapInsert state.results bb result } := by
  refine ⟨?_, hva.2⟩
  intro pdds hpdds
  rcases mem_mapValues_mapInsert hpdds with rfl | hold
  · exact hres
  · exact hva.1 pdds hold

/-- The full `validAnalysisState` postcondition for
    `computeEntry`'s function body. The proof splits on the two
    nested equation-capturing matches (the `mapGet` lookup and
    the `analyzeBlock` call), discharging the trivial arms and
    delegating the live arm to `pushToSuccessors_preserves_…`
    composed with `updateResults_preserves_…` and
    `computeEntry_exit_validPcgData`. -/
theorem validAnalysisState_of_computeEntry_body
    (body : Body) (state : AnalysisState) (bb : BasicBlockIdx)
    (h_validBody : validBody body)
    (h_validAnalysisState : validAnalysisState body state) :
    (match (match h_entry : mapGet state.entryStates bb with
            | .none => some state
            | .some entry =>
                match h_result : PcgData.analyzeBlock entry body bb h_validBody with
                | .none => none
                | .some result =>
                    let exit := match result.getLast? with
                                | .some last => last.states.postMain
                                | .none => entry
                    let succs := termSuccessors body.blocks[bb.index]!.terminator
                    let results1 := mapInsert state.results bb result
                    let state1 := { state with results := results1 }
                    some (pushToSuccessors state1 exit succs
                      (computeEntry_pushToSuccessors_precond
                        body state exit h_validAnalysisState
                        (computeEntry_exit_validPcgData
                          body state bb h_validBody h_validAnalysisState
                          entry (mem_mapValues_of_mapGet_eq_some h_entry)
                          result h_result)))) with
     | .none => true
     | .some s => validAnalysisState body s) := by
  split
  next h_outer =>
    -- Outer match returned `none`: only possible if `analyzeBlock = none`.
    trivial
  next s h_outer =>
    -- Outer match returned `some s`: figure out which inner arm produced it.
    split at h_outer
    · -- mapGet = none arm: outer = some state
      injection h_outer with h_eq
      rw [← h_eq]
      exact h_validAnalysisState
    · -- mapGet = some entry arm: outer = inner-match result
      rename_i entry h_entry
      split at h_outer
      · -- analyzeBlock = none → outer = none, contradicts h_outer
        nomatch h_outer
      · -- analyzeBlock = some result → outer = some (pushToSuccessors …)
        rename_i result h_result
        injection h_outer with h_eq
        rw [← h_eq]
        apply pushToSuccessors_preserves_validAnalysisState
        · exact updateResults_preserves_validAnalysisState body state bb result
            h_validAnalysisState
            (PcgData.analyzeBlock_all_validPcgDomainData h_validBody h_result
              (h_validAnalysisState.2 entry
                (mem_mapValues_of_mapGet_eq_some h_entry)))
        · exact computeEntry_exit_validPcgData body state bb h_validBody
            h_validAnalysisState entry
            (mem_mapValues_of_mapGet_eq_some h_entry) result h_result

}

defFn computeEntry (.plain "computeEntry")
  (doc! "Forward step for one basic block. Reads the pending entry state for `bb` from \
    `state.entryStates`, runs `PcgData.analyzeBlock` to obtain the per-step results, inserts those \
    results into `state.results`, and joins the post-main exit state into the pending entry of every \
    successor of `bb`. Blocks with no pending entry are unreachable so far in the traversal and are \
    returned without change. Returns `None` if `PcgData.analyzeBlock` fails.")
  (body "The function body." : Body)
  (state "The current analysis state." : AnalysisState)
  (bb "The block to step over." : BasicBlockIdx)
  requires validBody body, validAnalysisState body state
  ensures match result with
    | .none => true
    | .some s => validAnalysisState body s
    end
    via exact validAnalysisState_of_computeEntry_body body state bb h_validBody h_validAnalysisState
  : Option AnalysisState :=
    match h_entry : mapGet state↦entryStates bb with
    | .none => Some state
    | .some entry =>
        -- `match h_result :` (rather than the `←` Option-bind
        -- form) captures the equation `analyzeBlock _ _ _ _ =
        -- some result` so the post-call `exit` is provably
        -- `validPcgData body`-valid via the
        -- `analyzeBlock_last_postMain_validPcgData` chain
        -- through `computeEntry_exit_validPcgData`.
        match h_result : PcgData.analyzeBlock
            entry body bb proof[h_validBody] with
        | .none => None
        | .some result =>
            let exit :=
              match result·getLast? with
              | .some last => last↦states↦postMain
              | .none => entry
              end ;
            let succs := termSuccessors
              ((body↦blocks ! bb↦index)↦terminator) ;
            let results1 :=
              mapInsert state↦results bb result ;
            let state1 := state[results => results1] ;
            Some (pushToSuccessors state1 exit succs
              proof[computeEntry_pushToSuccessors_precond
                body state exit h_validAnalysisState
                (computeEntry_exit_validPcgData
                  body state bb h_validBody h_validAnalysisState
                  entry
                  (mem_mapValues_of_mapGet_eq_some h_entry)
                  result h_result)])
        end
    end

-- ══════════════════════════════════════════════
-- Iterate the RPO list, threading the analyzed map
-- ══════════════════════════════════════════════

-- Destructuring `computeEntry`'s subtype-wrapped result binds
-- `h_post` to the postcondition — `validAnalysisState body
-- state1` once the `Some state1` branch has refined the
-- predicate's match — which discharges `analyzeRpo`'s
-- `validAnalysisState` precondition at the recursive call.
defFn analyzeRpo (.plain "analyzeRpo")
  (doc! "Walk the reverse-postorder list, processing each block in turn with #computeEntry. The \
    analysis state — both the accumulated per-block results and the pending entry-state map — is \
    threaded through the traversal. Returns `None` as soon as #computeEntry fails on any block.")
  (body "The function body." : Body)
  (state "The current analysis state." : AnalysisState)
  (rpo "Remaining blocks to process, in reverse postorder."
      : List BasicBlockIdx)
  requires validBody body, validAnalysisState body state
  : Option AnalysisState :=
    match rpo with
    | [] => Some state
    | bb :: rest =>
        match computeEntry body state bb
            proof[h_validBody] proof[h_validAnalysisState] with
        | ⟨.none, _⟩ => None
        | ⟨.some state1, h_post⟩ =>
            analyzeRpo body state1 rest
        end
    end

-- ══════════════════════════════════════════════
-- Top-level entry point
-- ══════════════════════════════════════════════

-- Lemmas used to discharge `analyzeRpo`'s
-- `validAnalysisState` precondition for `analyzeBody`'s initial
-- state, which has `mapEmpty` per-block results and a
-- `mapSingleton ⟨0⟩ (PcgData.init body)` entry-state map. The
-- chain factors through three steps: (1) the value list of an
-- empty `Map` is `[]`; (2) `OwnedState.initial body` produces
-- exactly `body.decls.length` locals — so the initial PCG
-- satisfies `validPcgData body`; and (3) those two combine via
-- `mem_mapValues_mapInsert` to discharge the conjunction
-- `validAnalysisState` unfolds to.
defRaw inFns => {
private theorem mapValues_empty
    {κ : Type} [BEq κ] [Hashable κ] {ν : Type} :
    mapValues (∅ : Map κ ν) = [] := by
  unfold mapValues
  rw [Std.HashMap.fold_eq_foldl_toList,
    Std.HashMap.toList_empty]
  rfl

private theorem OwnedState.initial_locals_length (body : Body) :
    (OwnedState.initial body).locals.length =
      body.decls.length := by
  unfold OwnedState.initial
  simp

private theorem PcgData.init_validPcgData (body : Body) :
    validPcgData body (PcgData.init body) := by
  show (PcgData.init body).os.locals.length =
    body.decls.length
  unfold PcgData.init
  exact OwnedState.initial_locals_length body

private theorem validAnalysisResults_mapEmpty (body : Body) :
    validAnalysisResults body
      (∅ : Map BasicBlockIdx (List PcgDomainData)) := by
  show ∀ pdds ∈ mapValues
        (∅ : Map BasicBlockIdx (List PcgDomainData)),
       ∀ pdd ∈ pdds, validPcgDomainData body pdd
  intro pdds hpdds
  rw [mapValues_empty] at hpdds
  exact (List.not_mem_nil hpdds).elim

private theorem analyzeBody_state0_validAnalysisState
    (body : Body) :
    validAnalysisState body
      ⟨∅,
        mapSingleton (⟨0⟩ : BasicBlockIdx)
          (PcgData.init body)⟩ := by
  refine ⟨validAnalysisResults_mapEmpty body, ?_⟩
  intro pcg hpcg
  rcases mem_mapValues_mapInsert hpcg with rfl | hold
  · exact PcgData.init_validPcgData body
  · rw [mapValues_empty] at hold
    exact (List.not_mem_nil hold).elim
}

defFn analyzeBody (.plain "analyzeBody")
  (doc! "Run a single forward dataflow pass of \
    `PcgData.analyzeBlock` over every basic block of a \
    function body in reverse postorder, returning the \
    per-block analysis results. The entry state of block 0 \
    is constructed from the body via #PcgData.init; every other \
    block's entry state is the join of the post-main exit \
    states of its already-analyzed predecessors. Back edges \
    are ignored — predecessors reached only via a back edge \
    do not contribute to the join, so the analysis runs \
    once per block. Returns `None` if \
    `PcgData.analyzeBlock` fails on any block.")
  (body "The function body." : Body)
  requires validBody body
  : Option AnalysisResults :=
    let init := PcgData.init body ;
    let rpo := reversePostorder body ;
    let entryStates0 :=
      mapSingleton BasicBlockIdx⟨0⟩ init ;
    let state0 := AnalysisState⟨mapEmpty‹›, entryStates0⟩ ;
    let final ← analyzeRpo
      body state0 rpo proof[h_validBody]
      proof[analyzeBody_state0_validAnalysisState body] ;
    Some final↦results
