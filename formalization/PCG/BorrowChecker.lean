import MIR.Body

defStruct BorrowChecker (.doc (.plain "bc"),
    .doc (.plain "BorrowChecker"))
  "BorrowCheckers"
  "A borrow-checker oracle exposing the subset of \
   Polonius-style facts needed by the PCG: for each \
   origin (region variable), whether it is live at a \
   given MIR location."
where
  | origin_live_at "Whether the given origin is live at \
       the given MIR location."
      : RegionVid → Location → Bool
  deriving Inhabited
