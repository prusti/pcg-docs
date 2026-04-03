import Shared.DefEnum
import Shared.DefStruct

defStruct RegionVid (.text "vid")
  "A region variable identifier."
where
  | id "The region variable id." : Nat

defStruct EarlyBoundRegion (.text "eb")
  "An early-bound region, identified by its index \
   in the function's generic parameter list."
where
  | index "The index in the generic parameter list." : Nat

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
