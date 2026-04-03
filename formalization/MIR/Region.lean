/-- A region variable identifier, representing a unique region
    inferred by the borrow checker. -/
structure RegionVid where
  id : Nat
  deriving DecidableEq, Repr

/-- An early-bound region, identified by its index in the
    function's generic parameter list. -/
structure EarlyBoundRegion where
  index : Nat
  deriving DecidableEq, Repr

/-- A region (lifetime) in the MIR.

    Corresponds to the definition in `definitions/regions.md`:
    - `vid`: A `RegionVid` (region variable identifier)
    - `static`: The `'static` lifetime
    - `earlyBound`: An early-bound region from generic parameters -/
inductive Region where
  | vid (v : RegionVid)
  | static
  | earlyBound (eb : EarlyBoundRegion)
  deriving DecidableEq, Repr
