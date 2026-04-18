import MIR.Body
import Core.Dsl.DefFn

/-! # Validity conditions for borrow PCG edges

This module formalises the *validity conditions* described in
`definitions/validity-conditions.md`. A borrow PCG edge carries
a validity condition `pc` that picks out the execution paths
under which the edge is valid.

`pc.allowed` maps each *relevant* source block to the set of
allowed target blocks. A block `b` outside the domain of the
map (equivalently, with an empty allowed-target set) imposes
no constraint at `b`. -/

defStruct BranchChoice (.doc (.plain "d"),
    .doc (.plain "BranchChoice"))
  "Branch Choices"
  "An ordered pair of basic blocks (source, target) representing \
   a single control-flow transition from source to target."
where
  | source "The source basic block." : BasicBlockIdx
  | target "The target basic block." : BasicBlockIdx
  deriving Repr

defStruct ExecutionPath (.doc (.plain "p"),
    .doc (.plain "ExecutionPath"))
  "Execution Paths"
  "An execution path leading to a basic block: an ordered list \
   of blocks ending at that block."
where
  | blocks "The blocks in the path, in execution order."
      : List BasicBlockIdx
  deriving Repr

namespace ExecutionPath

defFn choices (.plain "choices")
  (.plain "The sequence of branch choices induced by adjacent \
    block pairs in the execution path.")
  (path "The execution path." : ExecutionPath)
  : List BranchChoice where
  | ⟨[]⟩ => []
  | ⟨[_]⟩ => []
  | ⟨b₀ :: (b₁ :: rest)⟩ =>
      BranchChoice⟨b₀, b₁⟩ ::
        choices ‹ExecutionPath⟨b₁ :: rest⟩›

end ExecutionPath

defStruct ValidityConditions (.doc (.plain "pc"),
    .doc (.plain "ValidityConditions"))
  "Validity Conditions"
  "Validity conditions associated with a borrow PCG edge: a \
   partial map from each relevant source block to the set of \
   allowed target blocks at that source."
where
  | allowed "Map from each relevant source block to the set of \
       allowed target blocks at that source."
      : Map BasicBlockIdx (Set BasicBlockIdx)
  deriving Repr

namespace ValidityConditions

defFn empty (.plain "empty")
  (.plain "The empty validity conditions: no block is relevant.")
  : ValidityConditions :=
    ValidityConditions⟨mapEmpty‹›⟩

defFn singleton (.plain "singleton")
  (.plain "The validity conditions whose only allowed transition \
    is the given branch choice (its source maps to a singleton \
    set containing its target).")
  (d "The branch choice." : BranchChoice)
  : ValidityConditions :=
    ValidityConditions⟨
      mapSingleton ‹d↦source, ⦃d↦target⦄›⟩

defFn union (.plain "union")
  (.plain "Pointwise union of two validity conditions: for \
    every source block, the allowed-target set is the union \
    of the two operands' allowed-target sets at that source.")
  (pc₁ "First validity conditions." : ValidityConditions)
  (pc₂ "Second validity conditions." : ValidityConditions)
  : ValidityConditions :=
    ValidityConditions⟨
      mapUnionSets ‹pc₁↦allowed, pc₂↦allowed›⟩

end ValidityConditions
