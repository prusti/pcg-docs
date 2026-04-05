import Core.Dsl.DefEnum
import Core.Dsl.DefStruct

defStruct RegionVid (.plain "vid")
  "A region variable identifier."
where
  | id "The region variable id." : Nat

defStruct EarlyBoundRegion (.plain "eb")
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
    (.doc (.plain "vid"), .sym .lparen,
     #v, .sym .rparen)
  | static
    "The 'static lifetime."
    (.doc (.code "'static"))
  | earlyBound (eb : EarlyBoundRegion)
    "An early-bound region from generic parameters."
    (.doc (.plain "early"), .sym .lparen,
     #eb, .sym .rparen)
