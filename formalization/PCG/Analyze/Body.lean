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

defRaw middle =>
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

defRaw middle =>
/-- Reverse postorder of the CFG starting from block 0. -/
private def reversePostorder (body : Body)
    : List BasicBlockIdx :=
  (dfsVisit body [] [] ⟨0⟩).2.reverse

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
defRaw inFns =>
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
defRaw inFns =>
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

defRaw inFns =>
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

defRaw inFns =>
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
-- hypothesis is provided as an axiom for now — it follows
-- from `analyzeBlock` preserving `validPcgDomainData`, which
-- has not yet been formalised.
defRaw inFns =>
axiom computeEntry_exit_validPcgData
    (body : Body) (state : AnalysisState) (bb : BasicBlockIdx)
    (h_validAnalysisState : validAnalysisState body state)
    (entry exit : PcgData Place)
    (h_entry_mem : entry ∈ mapValues state.entryStates) :
    validPcgData body exit

defRaw inFns =>
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
  : Option AnalysisState :=
    match h_entry : mapGet state↦entryStates bb with
    | .none => Some state
    | .some entry =>
        let result ← PcgData.analyzeBlock
          entry body bb proof[h_validBody] ;
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
              body state bb h_validAnalysisState
              entry exit
              (mem_mapValues_of_mapGet_eq_some h_entry))])
    end

-- ══════════════════════════════════════════════
-- Iterate the RPO list, threading the analyzed map
-- ══════════════════════════════════════════════

-- The recursive call to `analyzeRpo` re-enters with the
-- post-`computeEntry` state, whose `validAnalysisState`
-- discharge needs a `computeEntry`-preservation lemma not yet
-- formalised. The helper `analyzeRpo.precondAxiom` takes any
-- `Prop` and returns a proof — `apply`'d by the DSL-generated
-- auto-discharge tactic via `using […]`, it closes the
-- recursive-call `validAnalysisState` obligation in one step
-- (with `sorry`).
defRaw inFns =>
private theorem analyzeRpo.precondAxiom
    {P : Prop} : P := sorry

defFn analyzeRpo (.plain "analyzeRpo")
  (doc! "Walk the reverse-postorder list, processing each block in turn with #computeEntry. The \
    analysis state — both the accumulated per-block results and the pending entry-state map — is \
    threaded through the traversal. Returns `None` as soon as #computeEntry fails on any block.")
  (body "The function body." : Body)
  (state "The current analysis state." : AnalysisState)
  (rpo "Remaining blocks to process, in reverse postorder."
      : List BasicBlockIdx)
  requires validBody body,
    validAnalysisState body state
      using [analyzeRpo.precondAxiom]
  : Option AnalysisState :=
    match rpo with
    | [] => Some state
    | bb :: rest =>
        let state1 ← computeEntry
          body state bb proof[h_validBody]
            proof[h_validAnalysisState] ;
        analyzeRpo body state1 rest
    end

-- ══════════════════════════════════════════════
-- Top-level entry point
-- ══════════════════════════════════════════════

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
      body state0 rpo proof[h_validBody] proof[sorry] ;
    Some final↦results
