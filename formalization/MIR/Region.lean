import Shared.DefEnum

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

defEnum Region (.italic (.text "r"))
  "A region (lifetime) in the MIR. \
   See definitions/regions.md."
where
  | vid (v : RegionVid)
    "A region variable identifier."
    (.text "vid")
    (.text "vid")
  | static
    "The 'static lifetime."
    (.code "'static")
    (.code "'static")
  | earlyBound (eb : EarlyBoundRegion)
    "An early-bound region from generic parameters."
    (.text "earlyBound")
    (.text "earlyBound")
