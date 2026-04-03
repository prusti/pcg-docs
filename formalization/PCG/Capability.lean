import MIR.Ty

/-- A capability describes the actions permitted on a place at a
    particular program point.

    From `overview/capabilities.md`:
    - `exclusive`: Can be read, written, or mutably borrowed
    - `read`: Can be read; shared borrows can be created
    - `write`: Can be written to (e.g. behind an exclusive reference)
    - `shallowExclusive`: Used for the intermediate state when
      converting a raw pointer to a `Box` -/
inductive Capability where
  | exclusive
  | read
  | write
  | shallowExclusive
  deriving DecidableEq, Repr

namespace Capability

/-- A capability that permits reading from the place. -/
def canRead : Capability → Bool
  | .exclusive => true
  | .read => true
  | .write => false
  | .shallowExclusive => false

/-- A capability that permits writing to the place. -/
def canWrite : Capability → Bool
  | .exclusive => true
  | .read => false
  | .write => true
  | .shallowExclusive => true

/-- A capability that permits creating a mutable borrow. -/
def canMutBorrow : Capability → Bool
  | .exclusive => true
  | .read => false
  | .write => false
  | .shallowExclusive => false

/-- A capability that permits creating a shared borrow. -/
def canSharedBorrow : Capability → Bool
  | .exclusive => true
  | .read => true
  | .write => false
  | .shallowExclusive => false

/-- Downgrade a capability when a shared borrow is created to a
    pre- or postfix of the place.

    From `overview/capabilities.md`:
    "A place p with capability E is downgraded to R if a shared borrow
    is created to a place that is a pre- or postfix of p." -/
def downgradeForSharedBorrow : Capability → Capability
  | .exclusive => .read
  | other => other

/-- Downgrade a capability when dereferencing a reference.

    From `overview/capabilities.md`:
    - Shared reference dereference: downgrade to `R`
    - Exclusive reference dereference: downgrade to `W` -/
def downgradeForDeref (m : Mutability) : Capability → Capability
  | .exclusive => match m with
    | .shared => .read
    | .mutable => .write
  | other => other

end Capability
