/-- A partial order: reflexive, transitive, antisymmetric. -/
class PartialOrder (α : Type) extends LE α where
  /-- `a ≤ a` -/
  le_refl : ∀ (a : α), a ≤ a
  /-- If `a ≤ b` and `b ≤ c` then `a ≤ c`. -/
  le_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
  /-- If `a ≤ b` and `b ≤ a` then `a = b`. -/
  le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b

/-- A lattice is a partial order with binary supremum and infimum. -/
class Lattice (α : Type) extends PartialOrder α where
  /-- Binary supremum (join). -/
  sup : α → α → α
  /-- Binary infimum (meet). -/
  inf : α → α → α
  /-- `a ≤ sup a b` -/
  le_sup_left : ∀ (a b : α), a ≤ sup a b
  /-- `b ≤ sup a b` -/
  le_sup_right : ∀ (a b : α), b ≤ sup a b
  /-- If `a ≤ c` and `b ≤ c` then `sup a b ≤ c`. -/
  sup_le : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c
  /-- `inf a b ≤ a` -/
  inf_le_left : ∀ (a b : α), inf a b ≤ a
  /-- `inf a b ≤ b` -/
  inf_le_right : ∀ (a b : α), inf a b ≤ b
  /-- If `c ≤ a` and `c ≤ b` then `c ≤ inf a b`. -/
  le_inf : ∀ (a b c : α), c ≤ a → c ≤ b → c ≤ inf a b

/-- A bounded lattice has a top and bottom element. -/
class BoundedLattice (α : Type) extends Lattice α where
  /-- The top element. -/
  top : α
  /-- The bottom element. -/
  bot : α
  /-- Every element is ≤ top. -/
  le_top : ∀ (a : α), a ≤ top
  /-- Bottom is ≤ every element. -/
  bot_le : ∀ (a : α), bot ≤ a
