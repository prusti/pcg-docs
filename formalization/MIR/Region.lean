import Core.Dsl.DefEnum
import Core.Dsl.DefStruct

defStruct RegionVid (.text "vid",
    .text "RegionVid")
  "Region Variables"
  (.plain "A region variable identifier.")
where
  | id "The region variable id." : Nat

defStruct EarlyBoundRegion (.text "eb",
    .text "EarlyBoundRegion")
  "Early-Bound Regions"
  (.plain "An early-bound region, identified by its index \
   in the function's generic parameter list.")
where
  | index "The index in the generic parameter list."
      : Nat

defEnum Region (.raw "r", .raw "R")
  "Regions"
  (doc! "A region (lifetime) in the MIR. See `definitions/regions.md`.")
where
  | vid (v : RegionVid)
    "A region variable identifier."
  | static
    "The 'static lifetime."
    (.doc (.code "'static"))
  | earlyBound (eb : EarlyBoundRegion)
    "An early-bound region from generic parameters."
