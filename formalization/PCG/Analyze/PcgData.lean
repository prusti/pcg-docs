import Core.Dsl.DefFn
import Core.Dsl.DefRaw
import MIR.Body
import PCG.Analyze.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.Capability
import PCG.EvalStmtPhase
import PCG.Obtain.PcgData
import PCG.PcgData
import PCG.PcgDomainData

-- ══════════════════════════════════════════════
-- Stepping the PCG across a single statement phase
-- ══════════════════════════════════════════════

namespace PcgData

defFn obtainTriples (.plain "obtainTriples")
  (.plain "Apply obtain for each triple's pre-condition \
   capability in turn, threading the resulting PCG data \
   through. Returns None as soon as any obtain fails. The \
   precondition that every triple's place is valid in the \
   body discharges the corresponding precondition of obtain \
   at each step.")
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (triples "The triples whose pre-conditions to obtain."
      : List PlaceTriple)
  requires triples·forAll fun t => validPlace body t↦place
  : Option (PcgData Place) where
  | pd ; _ ; [] => Some pd
  | pd ; body ; t :: rest =>
      let pd' ← obtain pd body t↦place t↦pre proof[h_pre0 t (List.mem_cons_self ..)] ;
      obtainTriples pd' body rest

-- The export auto-namespaces functions by their first
-- parameter's type, so `operandTriple`/`borrowTriple`/
-- `statementTriples`/`terminatorTriples`/`rvalueTriples` end up
-- under their respective enum/struct namespaces in the generated
-- module (in source they live at top level). Open all of them
-- here so the helper proofs below can refer to the unqualified
-- names in both builds.
defRaw inFns => {
open Operand Mutability Statement Terminator Rvalue AnalysisObject Ty Body

-- Lawful-equality / hashable instances on `Capability` and
-- `PlaceTriple`. The `Std.HashSet`-membership lemmas
-- (`mem_insert`, `mem_union_iff`, `mem_toList`, …) used by the
-- triple-validity proofs below need them. The DSL only derives
-- `BEq` and `Hashable` on enums, so the lawful variants are
-- spelled out by hand: each `==` case either reduces to `rfl`
-- (matching constructors) or contradicts the `h : a == b`
-- hypothesis (mismatched constructors give `h : false = true`).
private instance instReflBEqCapability : ReflBEq Capability where
  rfl := by intro c; cases c <;> rfl

private instance instLawfulBEqCapability : LawfulBEq Capability where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | cases h

private instance instLawfulHashableCapability : LawfulHashable Capability where
  hash_eq {a b} h := by
    have : a = b := LawfulBEq.eq_of_beq h
    subst this; rfl

deriving instance ReflBEq, LawfulBEq for PlaceTriple

private instance instLawfulHashablePlaceTriple : LawfulHashable PlaceTriple where
  hash_eq {a b} h := by
    have : a = b := LawfulBEq.eq_of_beq h
    subst this; rfl

-- Generic `Set α = Std.HashSet α` toList-membership decomposition
-- lemmas. They are spelled in this file (rather than promoted to
-- `Runtime/Set.lean`) so they only impose `LawfulBEq` /
-- `LawfulHashable` requirements where the consumers actually
-- need them.
private theorem not_mem_empty_toList {α} [BEq α] [Hashable α]
    {t : α} : t ∉ (∅ : Set α).toList := by
  rw [Std.HashSet.toList_empty]; exact List.not_mem_nil

private theorem mem_singleton_toList {α} [BEq α] [LawfulBEq α]
    [Hashable α] [LawfulHashable α] {a t : α}
    (h : t ∈ (Set.singleton a).toList) : t = a := by
  unfold Set.singleton at h
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_insert] at h
  rcases h with h | h
  · exact (LawfulBEq.eq_of_beq h).symm
  · exact absurd h Std.HashSet.not_mem_empty

private theorem mem_set_singleton {α} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (a : α) :
    a ∈ (Set.singleton a) := by
  unfold Set.singleton
  exact Std.HashSet.mem_insert_self

private theorem mem_option_some_toSet {α} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (a : α) :
    a ∈ ((some a : Option α).toSet) := by
  unfold Option.toSet Set.ofOption
  exact mem_set_singleton a

private theorem mem_union_toList {α} [BEq α] [LawfulBEq α]
    [Hashable α] [LawfulHashable α] {s₁ s₂ : Set α} {t : α}
    (h : t ∈ (s₁ ++ s₂).toList) :
    t ∈ s₁.toList ∨ t ∈ s₂.toList := by
  rw [Std.HashSet.mem_toList] at h
  change t ∈ Set.union s₁ s₂ at h
  unfold Set.union at h
  rw [Std.HashSet.union_eq] at h
  by_cases h1 : t ∈ s₁
  · left; rw [Std.HashSet.mem_toList]; exact h1
  · right
    rw [Std.HashSet.mem_toList]
    exact Std.HashSet.mem_of_mem_union_of_not_mem_left h h1

private theorem foldl_union_mem_split {α β} [BEq β] [Hashable β]
    [EquivBEq β] [LawfulHashable β] (f : α → Std.HashSet β) (l : List α) (t : β) :
    ∀ acc : Std.HashSet β,
      t ∈ l.foldl (fun acc x => Std.HashSet.union acc (f x)) acc →
        t ∈ acc ∨ ∃ a ∈ l, t ∈ f a := by
  induction l with
  | nil => intro acc h; exact Or.inl h
  | cons x xs ih =>
    intro acc h
    rw [List.foldl_cons] at h
    rcases ih (acc.union (f x)) h with hAcc | ⟨a, ha, hb⟩
    · by_cases h1 : t ∈ acc
      · exact Or.inl h1
      · right
        refine ⟨x, List.mem_cons_self, ?_⟩
        rw [Std.HashSet.union_eq] at hAcc
        exact Std.HashSet.mem_of_mem_union_of_not_mem_left hAcc h1
    · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hb⟩

private theorem mem_flatMapList_toList {α β} [BEq β] [LawfulBEq β]
    [Hashable β] [LawfulHashable β] {l : List α} {f : α → Set β} {t : β}
    (h : t ∈ (Set.flatMapList l f).toList) :
    ∃ a ∈ l, t ∈ (f a).toList := by
  rw [Std.HashSet.mem_toList] at h
  unfold Set.flatMapList at h
  rcases foldl_union_mem_split f l t ∅ h with h | ⟨a, ha, hb⟩
  · exact absurd h Std.HashSet.not_mem_empty
  · exact ⟨a, ha, by rw [Std.HashSet.mem_toList]; exact hb⟩

private theorem foldl_union_mem_introduce {α β} [BEq β] [Hashable β]
    [EquivBEq β] [LawfulHashable β] (f : α → Set β) (b : β) :
    ∀ (l : List α) (acc : Std.HashSet β),
      (b ∈ acc ∨ ∃ a ∈ l, b ∈ f a) →
        b ∈ l.foldl (fun acc x => Std.HashSet.union acc (f x)) acc := by
  intro l
  induction l with
  | nil =>
    intro acc h
    rcases h with h | ⟨a, ha, _⟩
    · exact h
    · exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨a, ha, hb⟩
    · left
      rw [Std.HashSet.union_eq]
      exact Std.HashSet.mem_union_of_left h
    · rcases List.mem_cons.mp ha with rfl | hx
      · left
        rw [Std.HashSet.union_eq]
        exact Std.HashSet.mem_union_of_right hb
      · right; exact ⟨a, hx, hb⟩

private theorem mem_flatMapList_of_mem {α β} [BEq β] [Hashable β]
    [EquivBEq β] [LawfulHashable β] {l : List α} {f : α → Set β}
    {a : α} {b : β} (ha : a ∈ l) (hb : b ∈ f a) :
    b ∈ Set.flatMapList l f := by
  unfold Set.flatMapList
  exact foldl_union_mem_introduce f b l ∅ (Or.inr ⟨a, ha, hb⟩)

/-- A nil-projection place is a valid place whenever the
    underlying local is a valid local (`validProjTy _ []` holds
    by definition). -/
private theorem validPlace_of_validLocal_nilProj
    {body : Body} {lcl : Local} (h : validLocal body lcl) :
    validPlace body ⟨lcl, []⟩ := by
  refine ⟨h, ?_⟩
  show validProjTy _ []
  unfold validProjTy
  trivial

/-- Every triple in `(operandTriple o).toList` carries the
    operand's place; if the operand's place is valid in `body`,
    so is the triple's. -/
private theorem operandTriple_validPlace
    (body : Body) (o : Operand)
    (h : ∀ p, o.operandPlace = some p → validPlace body p)
    (t : PlaceTriple)
    (ht : t ∈ (operandTriple o).toList) :
    validPlace body t.place := by
  unfold operandTriple at ht
  cases o with
  | copy p =>
    have heq := mem_singleton_toList ht
    subst heq
    exact h p rfl
  | move p =>
    have heq := mem_singleton_toList ht
    subst heq
    exact h p rfl
  | const _ =>
    exact absurd ht not_mem_empty_toList

/-- Every triple in `(statementTriples s).toList` has a valid
    place when `s` is a valid statement. -/
private theorem statementTriples_validPlace
    (body : Body) (s : Statement) (h : validStatement body s)
    (t : PlaceTriple)
    (ht : t ∈ (statementTriples s).toList) :
    validPlace body t.place := by
  unfold statementTriples at ht
  cases s with
  | assign lhs rhs =>
    have hstmt :
        ∀ p ∈ Statement.statementPlaces (.assign lhs rhs),
          validPlace body p := h
    unfold rvalueTriples at ht
    cases rhs with
    | use o =>
      apply operandTriple_validPlace body o _ t ht
      intro p hp
      apply hstmt
      show p ∈ Statement.statementPlaces (.assign lhs (.use o))
      unfold Statement.statementPlaces
      simp only
      change p ∈ Set.union _ _
      unfold Set.union
      rw [Std.HashSet.union_eq]
      apply Std.HashSet.mem_union_of_right
      unfold Rvalue.rvaluePlace
      simp only
      rw [hp]
      exact mem_option_some_toSet p
    | ref _ m p =>
      have heq := mem_singleton_toList ht
      subst heq
      apply hstmt
      show (borrowTriple m p).place ∈
        Statement.statementPlaces (.assign lhs (.ref _ m p))
      unfold borrowTriple
      cases m <;> (
        simp only
        unfold Statement.statementPlaces
        simp only
        change p ∈ Set.union _ _
        unfold Set.union
        rw [Std.HashSet.union_eq]
        apply Std.HashSet.mem_union_of_right
        unfold Rvalue.rvaluePlace
        simp only
        exact mem_option_some_toSet p)
  | storageLive _ =>
    exact absurd ht not_mem_empty_toList
  | storageDead _ =>
    exact absurd ht not_mem_empty_toList

/-- Every triple in `(terminatorTriples term).toList` has a
    valid place when `term` is a valid terminator. -/
private theorem terminatorTriples_validPlace
    (body : Body) (term : Terminator) (h : validTerminator body term)
    (t : PlaceTriple)
    (ht : t ∈ (terminatorTriples term).toList) :
    validPlace body t.place := by
  unfold terminatorTriples at ht
  cases term with
  | goto _ =>
    exact absurd ht not_mem_empty_toList
  | switchInt o cs fb =>
    apply operandTriple_validPlace body o _ t ht
    intro p hp
    have hterm :
        ∀ p ∈ Terminator.terminatorPlaces (.switchInt o cs fb),
          validPlace body p := h
    apply hterm
    show p ∈ Terminator.terminatorPlaces (.switchInt o cs fb)
    unfold Terminator.terminatorPlaces
    simp only
    rw [hp]
    exact mem_option_some_toSet p
  | return_ =>
    exact absurd ht not_mem_empty_toList
  | unreachable =>
    exact absurd ht not_mem_empty_toList
  | drop _ _ =>
    exact absurd ht not_mem_empty_toList
  | call callee args dest next =>
    have hterm :
        ∀ p ∈ Terminator.terminatorPlaces
                (.call callee args dest next),
          validPlace body p := h
    rcases mem_union_toList ht with ht1 | ht2
    · apply operandTriple_validPlace body callee _ t ht1
      intro p hp
      apply hterm
      show p ∈ Terminator.terminatorPlaces
              (.call callee args dest next)
      unfold Terminator.terminatorPlaces
      simp only
      change p ∈ Set.union (Set.union _ _) _
      unfold Set.union
      rw [Std.HashSet.union_eq, Std.HashSet.union_eq]
      apply Std.HashSet.mem_union_of_left
      apply Std.HashSet.mem_union_of_right
      rw [hp]
      exact mem_option_some_toSet p
    · rcases mem_flatMapList_toList ht2 with ⟨a, ha, ht3⟩
      apply operandTriple_validPlace body a _ t ht3
      intro p hp
      apply hterm
      show p ∈ Terminator.terminatorPlaces
              (.call callee args dest next)
      unfold Terminator.terminatorPlaces
      simp only
      change p ∈ Set.union (Set.union _ _) _
      unfold Set.union
      rw [Std.HashSet.union_eq, Std.HashSet.union_eq]
      apply Std.HashSet.mem_union_of_right
      change p ∈ Set.flatMapList args
        (fun a => a.operandPlace.toSet)
      apply mem_flatMapList_of_mem ha
      rw [hp]
      exact mem_option_some_toSet p

/-- Every triple in `(operandTriples ao).toList` has a valid
    place when `ao` is a valid analysis object. -/
private theorem operandTriples_validPlace
    (body : Body) (ao : AnalysisObject)
    (h : validAnalysisObject body ao)
    (t : PlaceTriple)
    (ht : t ∈ (operandTriples ao).toList) :
    validPlace body t.place := by
  unfold operandTriples at ht
  cases ao with
  | stmt s =>
    have hs : validStatement body s := h
    exact statementTriples_validPlace body s hs t ht
  | terminator term =>
    have hs : validTerminator body term := h
    exact terminatorTriples_validPlace body term hs t ht

/-- Every triple in `(mainTriples ao).toList` has a valid place
    when `ao` is a valid analysis object. -/
private theorem mainTriples_validPlace
    (body : Body) (ao : AnalysisObject)
    (h : validAnalysisObject body ao)
    (t : PlaceTriple)
    (ht : t ∈ (mainTriples ao).toList) :
    validPlace body t.place := by
  unfold mainTriples at ht
  cases ao with
  | stmt s =>
    cases s with
    | assign lhs rhs =>
      have heq := mem_singleton_toList ht
      subst heq
      have hstmt :
          ∀ p ∈ Statement.statementPlaces (.assign lhs rhs),
            validPlace body p := h
      apply hstmt
      show lhs ∈ Statement.statementPlaces (.assign lhs rhs)
      unfold Statement.statementPlaces
      simp only
      change lhs ∈ Set.union _ _
      unfold Set.union
      rw [Std.HashSet.union_eq]
      apply Std.HashSet.mem_union_of_left
      exact mem_set_singleton lhs
    | storageLive lcl =>
      have heq := mem_singleton_toList ht
      subst heq
      exact validPlace_of_validLocal_nilProj h
    | storageDead lcl =>
      have heq := mem_singleton_toList ht
      subst heq
      exact validPlace_of_validLocal_nilProj h
  | terminator term =>
    have hterm : validTerminator body term := h
    cases term with
    | goto _ =>
      exact absurd ht not_mem_empty_toList
    | switchInt _ _ _ =>
      exact absurd ht not_mem_empty_toList
    | return_ =>
      exact absurd ht not_mem_empty_toList
    | unreachable =>
      exact absurd ht not_mem_empty_toList
    | drop p tgt =>
      have heq := mem_singleton_toList ht
      subst heq
      apply hterm
      show p ∈ Terminator.terminatorPlaces (.drop p tgt)
      unfold Terminator.terminatorPlaces
      simp only
      exact mem_set_singleton p
    | call callee args dest next =>
      have heq := mem_singleton_toList ht
      subst heq
      apply hterm
      show dest ∈ Terminator.terminatorPlaces
              (.call callee args dest next)
      unfold Terminator.terminatorPlaces
      simp only
      change dest ∈ Set.union (Set.union _ _) _
      unfold Set.union
      rw [Std.HashSet.union_eq, Std.HashSet.union_eq]
      apply Std.HashSet.mem_union_of_left
      apply Std.HashSet.mem_union_of_left
      exact mem_set_singleton dest

/-- The combined precondition `analyze` discharges for its
    `obtainTriples` call: every triple produced by the phase's
    `match` over `operandTriples ao` / `mainTriples ao` / `∅`
    has a place that is valid in `body`. The proof routes
    through `operandTriples_validPlace` and
    `mainTriples_validPlace`, applied to the
    `validAnalysisObject` postcondition of `getAnalysisObject`. -/
private theorem analyze_triples_validPlace
    (body : Body) (loc : Location) (h_validBody : validBody body)
    (phase : EvalStmtPhase) (t : PlaceTriple)
    (ht : t ∈ (match phase with
              | .preOperands =>
                  operandTriples
                    (getAnalysisObject body loc h_validBody).val
              | .preMain =>
                  mainTriples
                    (getAnalysisObject body loc h_validBody).val
              | .postOperands => (∅ : Set PlaceTriple)
              | .postMain => (∅ : Set PlaceTriple)).toList) :
    validPlace body t.place := by
  have h_ao :
      validAnalysisObject body
        (getAnalysisObject body loc h_validBody).val :=
    (getAnalysisObject body loc h_validBody).property
  cases phase with
  | preOperands =>
    exact operandTriples_validPlace body _ h_ao t ht
  | preMain =>
    exact mainTriples_validPlace body _ h_ao t ht
  | postOperands =>
    exact absurd ht not_mem_empty_toList
  | postMain =>
    exact absurd ht not_mem_empty_toList

}

defFn analyze (.plain "analyze")
  (doc! "Step the PCG state across a single statement evaluation phase. First looks up the analysis \
    object at `loc` in `body`. For `PreOperands` the pre-conditions of every #operandTriples entry \
    are obtained on the PCG; for `PreMain` the pre-conditions of every #mainTriples entry are \
    obtained. The two `Post` phases leave the PCG unchanged.")
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (loc "The program point at which the phase is evaluated."
      : Location)
  (phase "The evaluation phase." : EvalStmtPhase)
  requires validBody body
  : Option (PcgData Place) :=
    let ao := getAnalysisObject body loc proof[h_validBody] ·val ;
    let triples :=
      match phase with
        | .preOperands => operandTriples ao
        | .preMain => mainTriples ao
        | .postOperands => ∅
        | .postMain => ∅
      end ;
    -- The `validPlace` precondition of `obtainTriples` is
    -- discharged via #analyze_triples_validPlace, which folds
    -- the `validBody`/`validAnalysisObject` chain through the
    -- per-phase #operandTriples/#mainTriples constructions.
    obtainTriples pd body (triples·toList)
      proof[fun t ht =>
        analyze_triples_validPlace body loc h_validBody phase t ht]

defFn analyzeAt (.plain "analyzeAt")
  (doc! "Step the PCG state across all four evaluation phases at a single location, threading each \
    phase's output into the next. The returned #PcgDomainData carries the incoming PCG data as its \
    entry state and the four per-phase states produced by `analyze`. Returns `None` if any phase \
    fails.")
  (pd "The incoming PCG data, at the entry to the location."
      : PcgData Place)
  (body "The function body." : Body)
  (loc "The location at which to step (statement or \
       terminator)." : Location)
  requires validBody body
  : Option PcgDomainData :=
    let preOp ← analyze pd body loc .preOperands proof[h_validBody] ;
    let postOp ← analyze preOp body loc .postOperands proof[h_validBody] ;
    let preM ← analyze postOp body loc .preMain proof[h_validBody] ;
    let postM ← analyze preM body loc .postMain proof[h_validBody] ;
    Some DomainData⟨pd,
      EvalStmtData⟨preOp, postOp, preM, postM⟩⟩

defFn analyzeStmtsFrom (.plain "analyzeStmtsFrom")
  (doc! "Recursively step the PCG through the remaining statements of a basic block starting at \
    `idx`, followed by the basic block's terminator. Each step calls `analyzeAt` at `Location⟨bb, \
    idx⟩`, threading the post-main state into the next step. The empty-list case is the terminator \
    step at `stmtIdx == statements.length`. Returns the per-step #PcgDomainData values, or `None` if \
    any phase fails.")
  (pd "The PCG data on entry to the next step."
      : PcgData Place)
  (body "The function body." : Body)
  (bb "The basic block being analyzed." : BasicBlockIdx)
  (idx "The current statement index within the block."
      : Nat)
  (remaining "The statements that still need to be \
       processed, in order." : List Statement)
  requires validBody body
  : Option (List PcgDomainData) :=
    match remaining with
      | [] =>
          let dd ← analyzeAt pd body Location⟨bb, idx⟩ proof[h_validBody] ;
          Some [dd]
      | _ :: rest =>
          let dd ← analyzeAt pd body Location⟨bb, idx⟩ proof[h_validBody] ;
          -- Recursive call: the DSL auto-discharges
          -- `validBody` for recursive invocations, so no
          -- explicit proof argument here.
          let restDDs ← analyzeStmtsFrom
            (dd↦states↦postMain) body bb (idx + 1) rest ;
          Some (dd :: restDDs)
    end

defFn analyzeBlock (.plain "analyzeBlock")
  (doc! "Step the PCG state across an entire basic block: \
    one `analyzeAt` call per statement followed by one for \
    the terminator. Returns the resulting list of \
    #PcgDomainData values of length $__n+1__$, where $__n__$ \
    is the statement count, or `None` if any phase fails.")
  (pd "The PCG data on entry to the basic block."
      : PcgData Place)
  (body "The function body." : Body)
  (bb "The basic block to analyze." : BasicBlockIdx)
  requires validBody body
  : Option (List PcgDomainData) :=
    let block := body↦blocks ! bb↦index ;
    analyzeStmtsFrom pd body bb 0 block↦statements proof[h_validBody]

end PcgData
