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
  (.plain "List the basic-block successors of a terminator. \
    `goto`, `drop`, and `call` each have a single successor; \
    `return`, `unreachable`, and `switchInt` (in this \
    formalism) have none.")
  (t "The terminator." : Terminator)
  : List BasicBlockIdx where
  | .goto target => [target]
  | .switchInt _ => []
  | .return_ => []
  | .unreachable => []
  | .drop _ target => [target]
  | .call _ _ _ next => [next]

-- ══════════════════════════════════════════════
-- BasicBlockIdx list membership
-- ══════════════════════════════════════════════

defFn bbContains (.plain "bbContains")
  (.plain "Whether a basic-block index appears in a list, \
    compared by `index`.")
  (xs "The list to search." : List BasicBlockIdx)
  (b "The block index to look for." : BasicBlockIdx)
  : Bool where
  | [] ; _ => false
  | x :: rest ; b =>
      if x↦index == b↦index then true
      else bbContains ‹rest, b›

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
      | .switchInt _ => []
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

defFn pushOne (.plain "pushOne")
  (.seq [
    .plain "Join an exit state ", .code "exit",
    .plain " into the pending entry state of one successor \
     block. If ", .code "succ", .plain " already has a \
     pending entry, the two are combined with ",
    .code "PcgData.join", .plain "; otherwise the \
     contribution becomes the entry, rebased to ",
    .code "succ", .plain "."])
  (state "The current analysis state." : AnalysisState)
  (exit "The exit state of the just-processed predecessor."
      : PcgData Place)
  (succ "The successor block to push into."
      : BasicBlockIdx)
  : AnalysisState :=
    let newEntry :=
      match mapGet ‹state↦entryStates, succ› with
      | .some existing =>
          PcgData.join ‹existing, exit, succ›
      | .none =>
          PcgData⟨exit↦bg, exit↦ownedState, succ, None⟩
      end ;
    let entries1 :=
      mapInsert ‹state↦entryStates, succ, newEntry› ;
    state[entryStates => entries1]

defFn pushToSuccessors (.plain "pushToSuccessors")
  (.plain "Fold an exit state into every successor's pending \
    entry state via `pushOne`.")
  (state "The current analysis state." : AnalysisState)
  (exit "The exit state of the just-processed predecessor."
      : PcgData Place)
  (succs "Successor blocks of the predecessor."
      : List BasicBlockIdx)
  : AnalysisState where
  | state ; _ ; [] => state
  | state ; exit ; s :: rest =>
      pushToSuccessors ‹pushOne ‹state, exit, s›, exit, rest›

-- ══════════════════════════════════════════════
-- Forward step: process one block, propagate to successors
-- ══════════════════════════════════════════════

defFn computeEntry (.plain "computeEntry")
  (.seq [
    .plain "Forward step for one basic block. Reads the \
     pending entry state for ", .code "bb",
    .plain " from ", .code "state.entryStates",
    .plain ", runs ", .code "PcgData.analyzeBlock",
    .plain " to obtain the per-step results, inserts those \
     results into ", .code "state.results",
    .plain ", and joins the post-main exit state into the \
     pending entry of every successor of ", .code "bb",
    .plain ". Blocks with no pending entry are unreachable \
     so far in the traversal and are returned without \
     change. Returns ", .code "None",
    .plain " if ", .code "PcgData.analyzeBlock",
    .plain " fails."])
  (body "The function body." : Body)
  (state "The current analysis state." : AnalysisState)
  (bb "The block to step over." : BasicBlockIdx)
  : Option AnalysisState :=
    match mapGet ‹state↦entryStates, bb› with
    | .none => Some state
    | .some entry =>
        let result ← PcgData.analyzeBlock ‹entry, body, bb› ;
        let exit :=
          match result·getLast? with
          | .some last => last↦states↦postMain
          | .none => entry
          end ;
        let succs := termSuccessors
          ‹(body↦blocks ! bb↦index)↦terminator› ;
        let results1 :=
          mapInsert ‹state↦results, bb, result› ;
        let state1 := state[results => results1] ;
        Some (pushToSuccessors ‹state1, exit, succs›)
    end

-- ══════════════════════════════════════════════
-- Iterate the RPO list, threading the analyzed map
-- ══════════════════════════════════════════════

defFn analyzeRpo (.plain "analyzeRpo")
  (.seq [
    .plain "Walk the reverse-postorder list, processing each \
     block in turn with ", .code "computeEntry",
    .plain ". The analysis state — both the accumulated \
     per-block results and the pending entry-state map — is \
     threaded through the traversal. Returns ",
    .code "None", .plain " as soon as ",
    .code "computeEntry", .plain " fails on any block."])
  (body "The function body." : Body)
  (state "The current analysis state." : AnalysisState)
  (rpo "Remaining blocks to process, in reverse postorder."
      : List BasicBlockIdx)
  : Option AnalysisState :=
    match rpo with
    | [] => Some state
    | bb :: rest =>
        let state1 ← computeEntry ‹body, state, bb› ;
        analyzeRpo ‹body, state1, rest›
    end

-- ══════════════════════════════════════════════
-- Top-level entry point
-- ══════════════════════════════════════════════

defFn analyzeBody (.plain "analyzeBody")
  (.seq [
    .plain "Run a single forward dataflow pass of ",
    .code "PcgData.analyzeBlock",
    .plain " over every basic block of a function body in \
     reverse postorder, returning the per-block analysis \
     results. The entry state of block 0 is constructed from \
     the body via ", .code "OwnedState.initial",
    .plain " and an empty borrows graph; every other block's \
     entry state is the join of the post-main exit states of \
     its already-analyzed predecessors. Back edges are \
     ignored — predecessors reached only via a back edge do \
     not contribute to the join, so the analysis runs once \
     per block. Returns ", .code "None", .plain " if ",
    .code "PcgData.analyzeBlock",
    .plain " fails on any block."])
  (body "The function body." : Body)
  : Option AnalysisResults :=
    let init :=
      PcgData⟨BorrowsGraph⟨mapEmpty‹›⟩,
        OwnedState.initial ‹body›,
        BasicBlockIdx⟨0⟩, None⟩ ;
    let rpo := reversePostorder ‹body› ;
    let entryStates0 :=
      mapSingleton ‹BasicBlockIdx⟨0⟩, init› ;
    let state0 := AnalysisState⟨mapEmpty‹›, entryStates0⟩ ;
    let final ← analyzeRpo ‹body, state0, rpo› ;
    Some final↦results
