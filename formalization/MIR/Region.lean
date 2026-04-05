import Core.Dsl.DefEnum
import Core.Dsl.DefStruct

defStruct RegionVid (.math (.doc (.text "vid")))
  "A region variable identifier."
where
  | id "The region variable id." : Nat

defStruct EarlyBoundRegion (.math (.doc (.text "eb")))
  "An early-bound region, identified by its index \
   in the function's generic parameter list."
where
  | index "The index in the generic parameter list."
      : Nat

defEnum Region (.math (.var "r"))
  "A region (lifetime) in the MIR. \
   See definitions/regions.md."
where
  | vid (v : RegionVid)
    "A region variable identifier."
    (.doc (.text "vid("), #v, .doc (.text ")"))
  | static
    "The 'static lifetime."
    (.doc (.code "'static"))
  | earlyBound (eb : EarlyBoundRegion)
    "An early-bound region from generic parameters."
    (.doc (.text "early("), #eb, .doc (.text ")"))
