import Core.Dsl.DefFn
import MIR.Body
import PCG.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.Capability

defFn operandTriple (.plain "operandTriple")
  (doc! "The set of place triples implied by a single \
    operand: a `copy` yields a $__R__$ triple with no \
    post-condition; a `move` yields an $__E__$ triple with \
    post $__W__$; a constant contributes nothing.")
  (o "The operand." : Operand)
  : Set PlaceTriple where
  | .copy p =>
      ⦃PlaceTriple⟨p, Capability.read, None⟩⦄
  | .move p =>
      ⦃PlaceTriple⟨p, Capability.exclusive, Some Capability.write⟩⦄
  | .const _ => ∅

defFn borrowTriple (.plain "borrowTriple")
  (doc! "The place triple implied by a borrow of a place at \
    the given mutability: shared yields a $__R__$ triple with \
    no post-condition, mutable yields an $__E__$ triple with \
    post ∅.")
  (m "The borrow's mutability." : Mutability)
  (p "The borrowed place." : Place)
  : PlaceTriple where
  | .shared ; p =>
      PlaceTriple⟨p, Capability.read, None⟩
  | .mutable ; p =>
      PlaceTriple⟨p, Capability.exclusive, Some Capability.none⟩

defFn rvalueTriples (.plain "rvalueTriples")
  (.plain "The set of place triples implied by an rvalue: a \
   use contributes its operand's triple; a borrow \
   contributes the borrow's triple.")
  (rv "The rvalue." : Rvalue)
  : Set PlaceTriple where
  | .use o => operandTriple o
  | .ref _ m p => ⦃borrowTriple m p⦄

defFn statementTriples (.plain "statementTriples")
  (.plain "The set of place triples implied by a statement: \
   an assignment contributes its rvalue's triples; storage \
   markers contribute nothing.")
  (s "The statement." : Statement)
  : Set PlaceTriple where
  | .assign _ rhs => rvalueTriples rhs
  | .storageLive _ => ∅
  | .storageDead _ => ∅

defFn terminatorTriples (.plain "terminatorTriples")
  (.plain "The set of place triples implied by a terminator: \
   only operand-bearing variants contribute.")
  (t "The terminator." : Terminator)
  : Set PlaceTriple where
  | .goto _ => ∅
  | .switchInt o _ _ => operandTriple o
  | .return_ => ∅
  | .unreachable => ∅
  | .drop _ _ => ∅
  | .call callee args _ _ =>
      operandTriple callee ∪
        (args·setFlatMap fun a => operandTriple a)

defFn operandTriples (.plain "operandTriples")
  (doc! "The set of place triples implied by the operand and \
    borrow uses of places in an analysis object. A `copy` \
    operand or shared borrow yields a $__R__$ triple with no \
    post-condition; a `move` operand yields an $__E__$ triple \
    with post $__W__$; a mutable borrow yields an $__E__$ \
    triple with post ∅.")
  (ao "The analysis object." : AnalysisObject)
  : Set PlaceTriple where
  | .stmt s => statementTriples s
  | .terminator t => terminatorTriples t

defFn mainTriples (.plain "mainTriples")
  (doc! "The set of place triples implied by the main effect \
    of an analysis object. An assignment requires $__W__$ on \
    its destination and establishes $__E__$; `StorageLive` \
    transitions the local from ∅ to \
    $__E__$; `StorageDead` transitions it from $__E__$ back \
    to ∅; a `drop` consumes $__E__$ \
    and leaves ∅; a `call` requires \
    $__W__$ on its destination and establishes $__E__$; other \
    terminators contribute nothing.")
  (ao "The analysis object." : AnalysisObject)
  : Set PlaceTriple where
  | .stmt (.assign lhs _) =>
      ⦃PlaceTriple⟨lhs, Capability.write,
        Some Capability.exclusive⟩⦄
  | .stmt (.storageLive lcl) =>
      ⦃PlaceTriple⟨Place⟨lcl, []⟩, Capability.none,
        Some Capability.exclusive⟩⦄
  | .stmt (.storageDead lcl) =>
      ⦃PlaceTriple⟨Place⟨lcl, []⟩, Capability.exclusive,
        Some Capability.none⟩⦄
  | .terminator (.drop p _) =>
      ⦃PlaceTriple⟨p, Capability.exclusive,
        Some Capability.none⟩⦄
  | .terminator (.call _ _ dest _) =>
      ⦃PlaceTriple⟨dest, Capability.write,
        Some Capability.exclusive⟩⦄
  | .terminator _ => ∅

-- Local `Inhabited` instances scoped to this module so that
-- the `[i]!` indexing inside `getAnalysisObject` elaborates
-- against the source `defStruct`/`defEnum`s, which only
-- derive `Repr, BEq, Hashable`. The Lean exporter also adds
-- `deriving Inhabited` to the corresponding generated
-- declarations; the auto-derived defaults pick the *first*
-- constructor (e.g. `Terminator.goto default` rather than
-- `Terminator.unreachable`), which would change the
-- out-of-range arm of `getAnalysisObject` (because
-- `body.blocks[i]!` falls back to the `Inhabited BasicBlock`
-- default when `i` is out of range). To keep the in-tree
-- proof and the generated copy of `getAnalysisObject`
-- discharging the same out-of-range case, the same instances
-- are spliced into the generated module via `defRaw inFns =>`
-- below; later-declared instances take precedence in Lean's
-- instance resolution, so they outrank the auto-derived
-- defaults the exporter emits earlier in the file.
defRaw inFns =>
instance : Inhabited Terminator := ⟨.unreachable⟩

defRaw inFns =>
instance : Inhabited Statement := ⟨.storageLive ⟨0⟩⟩

defRaw inFns =>
instance : Inhabited BasicBlock := ⟨⟨[], .unreachable⟩⟩

-- Bridge from #validBody to the postcondition of
-- #getAnalysisObject: the if/then/else body of
-- #getAnalysisObject is a valid #AnalysisObject in `body`
-- whenever `body` itself is valid. The proof splits on the
-- `if`, then on whether `loc.block.index` is in range:
--
-- * In-range, statement arm — the indexed statement is in
--   the basic block's statement list, so #validBody's per-
--   block conjunct gives #validStatement directly.
-- * In-range, terminator arm — the basic block is in
--   `body.blocks`, so #validBody's per-block conjunct gives
--   #validTerminator on its terminator directly.
-- * Out-of-range — #getElem!_neg makes the indexed block the
--   `Inhabited` default `⟨[], .unreachable⟩`, whose
--   terminator is `.unreachable`. The `if` condition is then
--   `loc.stmtIdx < 0` (always false), so the result is
--   `.terminator .unreachable`, which has empty
--   #terminatorPlaces and so is trivially valid.
--
-- Stated and proved here so that #getAnalysisObject's
-- `ensures` clause can attach it via the DSL's `via`
-- extension. Wrapped in `defRaw inFns =>` so the lemma is
-- declared in the in-tree build (for the `via` to typecheck)
-- and is also re-emitted into the generated Lean export
-- right before #getAnalysisObject (so the exported `via`
-- block can resolve the same name).
defRaw inFns =>
theorem validAnalysisObject_of_getAnalysisObject_body
    (body : Body) (loc : Location)
    (h_validBody : validBody body) :
    validAnalysisObject body
      (let bb := body.blocks[loc.block.index]!;
       if loc.stmtIdx < bb.statements.length then
         AnalysisObject.stmt
           (bb.statements[loc.stmtIdx]!)
       else
         AnalysisObject.terminator bb.terminator) := by
  -- `validBody`'s relevant conjunct: every block's statements
  -- are valid statements and its terminator is a valid
  -- terminator. Specialise once up front so both `if` arms
  -- (and both branches of the in-/out-of-range split below)
  -- can pull from it.
  have h_blocks := h_validBody.2.2.1
  -- `simp only []` reduces the leading `let bb := …` so the
  -- subsequent `split` sees the exposed `if` directly.
  simp only []
  by_cases h_in : loc.block.index < body.blocks.length
  · -- In-range: `body.blocks[loc.block.index]!` is in
    -- `body.blocks`, so `h_blocks` specialises to it.
    have h_bb_mem :
        body.blocks[loc.block.index]! ∈ body.blocks := by
      rw [getElem!_pos body.blocks loc.block.index h_in]
      exact List.getElem_mem h_in
    have h_block := h_blocks _ h_bb_mem
    split
    · -- statement arm: indexed statement is in
      -- `bb.statements`, so `h_block.1` gives `validStatement`.
      rename_i h_lt
      simp only [validAnalysisObject]
      have h_stmt_mem :
          (body.blocks[loc.block.index]!).statements[
              loc.stmtIdx]! ∈
            (body.blocks[loc.block.index]!).statements := by
        rw [getElem!_pos
              (body.blocks[loc.block.index]!).statements
              loc.stmtIdx h_lt]
        exact List.getElem_mem h_lt
      exact h_block.1 _ h_stmt_mem
    · -- terminator arm: `h_block.2` is the validity of the
      -- block's terminator.
      simp only [validAnalysisObject]
      exact h_block.2
  · -- Out-of-range: the `Inhabited BasicBlock` default has an
    -- empty statements list (so the `if` falls into the
    -- terminator arm) and an `.unreachable` terminator (whose
    -- `terminatorPlaces` is empty), making the postcondition
    -- vacuously true.
    have h_default :
        body.blocks[loc.block.index]! =
          (default : BasicBlock) :=
      getElem!_neg body.blocks loc.block.index h_in
    rw [h_default]
    -- `default = ⟨[], .unreachable⟩`, so `bb.statements`
    -- is `[]` and the `if` falls through to the terminator
    -- arm. `loc.stmtIdx < 0` is false.
    simp only [show (default : BasicBlock).statements = []
                from rfl,
               List.length_nil, Nat.not_lt_zero, if_false,
               show (default : BasicBlock).terminator =
                    Terminator.unreachable from rfl,
               validAnalysisObject, validTerminator,
               Terminator.terminatorPlaces]
    -- Goal: `∀ p ∈ ∅, validPlace body p`; vacuous.
    intro p hp
    exact (Std.HashSet.not_mem_empty hp).elim

defFn getAnalysisObject (.plain "getAnalysisObject")
  (.plain "Look up the analysis object at a location in a body: \
   the statement at the given index when one exists at that \
   position, otherwise the basic block's terminator.")
  (body "The function body." : Body)
  (loc "The location." : Location)
  requires validBody body
  ensures validAnalysisObject body result
    via exact validAnalysisObject_of_getAnalysisObject_body body loc h_validBody
  : AnalysisObject :=
    let bb := body↦blocks ! loc↦block↦index ;
    if loc↦stmtIdx < bb↦statements·length then
      .stmt (bb↦statements ! loc↦stmtIdx)
    else
      .terminator bb↦terminator
