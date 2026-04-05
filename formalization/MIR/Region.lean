import Core.Dsl.DefEnum
import Core.Dsl.DefStruct

defStruct RegionVid (.text "vid")
  "A region variable identifier."
where
  | id "The region variable id." : Nat

defStruct EarlyBoundRegion (.text "eb")
  "An early-bound region, identified by its index \
   in the function's generic parameter list."
where
  | index "The index in the generic parameter list."
      : Nat

defEnum Region (.italic (.text "r"))
  "A region (lifetime) in the MIR. \
   See definitions/regions.md."
where
  | vid (v : RegionVid)
    "A region variable identifier."
    (.text "vid(", #v, .text ")")
  | static
    "The 'static lifetime."
    (.code "'static")
  | earlyBound (eb : EarlyBoundRegion)
    "An early-bound region from generic parameters."
    (.text "early(", #eb, .text ")")
