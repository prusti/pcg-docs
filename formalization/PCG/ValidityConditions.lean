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

defStruct BranchChoice (.text "d",
    .text "BranchChoice")
  "Branch Choices"
  (doc! "A branch choice \
    $_d_ ∈ _BranchChoice_$ \
    is an ordered pair of basic blocks representing a single \
    control-flow transition from a source block to a target \
    block.")
where
  | source "Source block." : BasicBlockIdx
  | target "Target block." : BasicBlockIdx
  deriving Repr

defStruct ExecutionPath (.text "p",
    .text "ExecutionPath")
  "Execution Paths"
  (doc! "An execution path \
    $_p_ ∈ _ExecutionPath_$ \
    is an ordered list of basic blocks leading to (and \
    ending at) a particular block.")
where
  | blocks "Blocks in execution order."
      : List BasicBlockIdx
  deriving Repr

namespace ExecutionPath

defFn choicesOfBlocks (.plain "choicesOfBlocks")
  (.plain "Branch choices induced by the given list of \
    execution-order blocks.")
  (blocks "The blocks in execution order."
      : List BasicBlockIdx)
  : List BranchChoice where
  | [] => []
  | [_] => []
  | b0 :: b1 :: rest =>
      BranchChoice⟨b0, b1⟩ ::
        choicesOfBlocks ‹b1 :: rest›

defFn choices (.plain "choices")
  (.plain "The sequence of branch choices induced by adjacent \
    block pairs in the execution path.")
  (path "The execution path." : ExecutionPath)
  : List BranchChoice :=
    choicesOfBlocks ‹path↦blocks›

end ExecutionPath

defStruct ValidityConditions (.text "pc",
    .text "ValidityConditions")
  "Validity Conditions"
  (doc! "Validity conditions \
    $_pc_ ∈ _ValidityConditions_$ \
    select the execution paths under which a borrow PCG \
    edge is valid: a partial map from each relevant source \
    block to the set of allowed target blocks at that \
    source.")
where
  | allowed "Allowed transitions per source block."
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

defFn join (.plain "join")
  (.plain "Pointwise join of two validity conditions: for \
    every source block, the allowed-target set is the union \
    of the two operands' allowed-target sets at that source.")
  (pc1 "First validity conditions." : ValidityConditions)
  (pc2 "Second validity conditions." : ValidityConditions)
  : ValidityConditions :=
    ValidityConditions⟨
      mapUnionSets ‹pc1↦allowed, pc2↦allowed›⟩

end ValidityConditions
