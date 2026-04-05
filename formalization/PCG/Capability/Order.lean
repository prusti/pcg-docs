import PCG.Capability
import Core.Dsl.DefOrder
import Core.Order

defOrder Capability where
  | exclusive > read
  | exclusive > shallowExclusive
  | shallowExclusive > write
  | write > none
  | read > none

namespace Capability

instance : PartialOrder Capability where
  le_refl a := by cases a <;> decide
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by
    cases a <;> cases b <;> decide

/-- Binary supremum (join) of capabilities. -/
def sup (a b : Capability) : Capability :=
  if a.le b then b else if b.le a then a else .exclusive

/-- Binary infimum (meet) of capabilities. -/
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
    cases a <;> cases b <;> cases c <;>
      simp [LE.le, le, sup]
  inf_le_left a b := by
    cases a <;> cases b <;> simp [LE.le, le, inf]
  inf_le_right a b := by
    cases a <;> cases b <;> simp [LE.le, le, inf]
  le_inf a b c := by
    cases a <;> cases b <;> cases c <;>
      simp [LE.le, le, inf]

instance : BoundedLattice Capability where
  top := .exclusive
  bot := .none
  le_top a := by cases a <;> decide
  bot_le a := by cases a <;> decide

end Capability
