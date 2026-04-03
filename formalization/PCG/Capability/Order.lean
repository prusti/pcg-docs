import PCG.Capability
import Shared.Order

namespace Capability

/-- Decidable ordering on capabilities.

    The Hasse diagram is:
    ```
          E
         / \
        R   W
        |   |
        |   e
         \ /
         none
    ``` -/
def le : Capability → Capability → Bool
  | .none, _ => true
  | .shallowExclusive, .shallowExclusive => true
  | .shallowExclusive, .write => true
  | .shallowExclusive, .exclusive => true
  | .read, .read => true
  | .read, .exclusive => true
  | .write, .write => true
  | .write, .exclusive => true
  | .exclusive, .exclusive => true
  | _, _ => false

instance : LE Capability where
  le a b := a.le b = true

instance instDecidableLE (a b : Capability) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.le b = true))

instance : PartialOrder Capability where
  le_refl a := by cases a <;> decide
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [LE.le, le]
  le_antisymm a b := by
    cases a <;> cases b <;> simp [LE.le, le]

/-- Binary supremum (join) of capabilities.

    For comparable elements, returns the greater. For incomparable
    pairs (R vs W, R vs e), the join is E. -/
def sup (a b : Capability) : Capability :=
  if a.le b then b else if b.le a then a else .exclusive

/-- Binary infimum (meet) of capabilities.

    For comparable elements, returns the lesser. For incomparable
    pairs, the meet is none. -/
def inf (a b : Capability) : Capability :=
  if a.le b then a else if b.le a then b else .none

instance : Lattice Capability where
  sup := sup
  inf := inf
  le_sup_left a b := by
    cases a <;> cases b <;> simp [LE.le, le, sup]
  le_sup_right a b := by
    cases a <;> cases b <;> simp [LE.le, le, sup]
  sup_le a b c := by
    cases a <;> cases b <;> cases c <;> simp [LE.le, le, sup]
  inf_le_left a b := by
    cases a <;> cases b <;> simp [LE.le, le, inf]
  inf_le_right a b := by
    cases a <;> cases b <;> simp [LE.le, le, inf]
  le_inf a b c := by
    cases a <;> cases b <;> cases c <;> simp [LE.le, le, inf]

instance : BoundedLattice Capability where
  top := .exclusive
  bot := .none
  le_top a := by cases a <;> decide
  bot_le a := by cases a <;> decide

end Capability
