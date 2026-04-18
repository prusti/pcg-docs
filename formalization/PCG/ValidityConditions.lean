import MIR.Body

/-! # Validity conditions for borrow PCG edges

This module formalises the *validity conditions* described in
`definitions/validity-conditions.md`. A borrow PCG edge carries
a validity condition `pc` that picks out the execution paths
under which the edge is valid.

Conceptually `pc` is a partial function
`BasicBlockIdx → 𝒫(BasicBlockIdx)` from *relevant* source
blocks to their *allowed* target blocks. A block `b` that is
outside the domain (equivalently, whose allowed-target set is
empty) imposes no constraint at `b`. -/

/-- A branch choice `bᵢ → bⱼ`: an ordered pair of basic blocks
    representing a single control-flow transition. -/
structure BranchChoice where
  /-- The source basic block. -/
  source : BasicBlockIdx
  /-- The target basic block. -/
  target : BasicBlockIdx
deriving Repr

/-- An *execution path* leading to a basic block: an ordered
    list of blocks ending at that block. The set of control-flow
    transitions taken along the path is given by
    `ExecutionPath.choices`. -/
abbrev ExecutionPath := List BasicBlockIdx

namespace ExecutionPath

/-- The sequence of branch choices induced by adjacent block
    pairs in the path. -/
def choices : List BasicBlockIdx → List BranchChoice
  | [] => []
  | [_] => []
  | b₀ :: tail@(b₁ :: _) => ⟨b₀, b₁⟩ :: choices tail

end ExecutionPath

/-- Validity conditions associated with a borrow PCG edge.

    Conceptually a partial map
    `pc : BasicBlockIdx → 𝒫(BasicBlockIdx)` from *relevant*
    source blocks to their *allowed* target blocks. We model
    `pc[b]` by the `Prop`-valued relation `allowed b`: a block
    `b` is *not relevant* (i.e. `pc[b] = ∅`) iff `allowed b`
    is identically false.

    See `definitions/validity-conditions.md`. -/
structure ValidityConditions where
  /-- `allowed b t` holds iff `t` is an allowed target for
      source block `b`. -/
  allowed : BasicBlockIdx → BasicBlockIdx → Prop

namespace ValidityConditions

/-- The *empty* validity conditions: no block is relevant,
    i.e. `pc[b] = ∅` for every `b`. -/
def empty : ValidityConditions := ⟨fun _ _ => False⟩

/-- A source block is *relevant* in `pc` iff it has at least
    one allowed target, i.e. iff `pc[b] ≠ ∅`. -/
def isRelevant (pc : ValidityConditions) (b : BasicBlockIdx) :
    Prop :=
  ∃ t, pc.allowed b t

/-- The pointwise *join* of two validity conditions:
    `(pc₁ ∪ pc₂)[b] = pc₁[b] ∪ pc₂[b]`. -/
def union (pc₁ pc₂ : ValidityConditions) : ValidityConditions :=
  ⟨fun b t => pc₁.allowed b t ∨ pc₂.allowed b t⟩

/-- The validity condition whose only allowed transition is
    `d.source → d.target`. -/
def singleton (d : BranchChoice) : ValidityConditions :=
  ⟨fun b t => b = d.source ∧ t = d.target⟩

/-- Extend `pc` by adding `d.target` to the allowed-target set
    at `d.source`. Corresponds to the `pc ∪ {b_f → b_n}` step
    in the inductive construction of an edge's validity
    conditions described in
    `definitions/validity-conditions.md`. -/
def insertChoice (pc : ValidityConditions) (d : BranchChoice) :
    ValidityConditions :=
  pc.union (singleton d)

/-- A branch choice `d = bₛ → bₜ` is *admitted* by `pc` iff
    either `bₛ` is not relevant in `pc`, or `bₜ` is in `pc`'s
    allowed-target set at `bₛ`. -/
def admits (pc : ValidityConditions) (d : BranchChoice) :
    Prop :=
  ¬ pc.isRelevant d.source ∨ pc.allowed d.source d.target

/-- An execution path is *valid* for `pc` iff every branch
    choice it induces is admitted. -/
def valid (pc : ValidityConditions) (path : ExecutionPath) :
    Prop :=
  ∀ d ∈ ExecutionPath.choices path, pc.admits d

/-! ## Monotonicity of membership under join

The proof sketch in `definitions/validity-conditions.md`
relies on the following monotonicity property of `union`:

> if `b' ∈ pc[b]` then `b' ∈ (pc ∪ pc')[b]` for any `pc'`.

Note that *admissibility* is not monotone in the same way,
because extending `pc` can promote a previously irrelevant
source block into the domain. The proof in the md file works
around this by simultaneously extending the path and the
conditions, so that any new relevance is accompanied by the
corresponding allowed target. -/

theorem allowed_union_left
    {pc₁ pc₂ : ValidityConditions} {b t : BasicBlockIdx}
    (h : pc₁.allowed b t) : (pc₁.union pc₂).allowed b t :=
  Or.inl h

theorem allowed_union_right
    {pc₁ pc₂ : ValidityConditions} {b t : BasicBlockIdx}
    (h : pc₂.allowed b t) : (pc₁.union pc₂).allowed b t :=
  Or.inr h

/-! ## Correctness (informal)

The md file states the central correctness theorem:

> For every borrow edge `e` in the PCG at location `l` and
> every execution path `d̄` to `l`, the corresponding borrow is
> live at `l` iff `d̄` satisfies the validity conditions of
> `e`.

Formalising either direction of this theorem requires a formal
definition of "the borrow edge `e`" and of "liveness of the
borrow at a location", neither of which is yet present in the
PCG Lean module. The proof sketch in
`definitions/validity-conditions.md` rests on
`allowed_union_left` / `allowed_union_right` above: when the
validity conditions grow via `union`, every previously allowed
target remains allowed. -/

end ValidityConditions
