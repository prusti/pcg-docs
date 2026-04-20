import MIR.Body
import PCG.PcgNode

defStruct BorrowChecker {P}
    (.doc (.plain "bc"),
     .doc (.plain "BorrowChecker"))
  "BorrowCheckers"
  (.plain "A borrow-checker oracle exposing the subset of \
   Polonius-style facts needed by the PCG: for each PCG \
   node, whether it is live at a given MIR location.")
where
  | isLive "Whether the given PCG node is live at the \
       given MIR location."
      : PcgNode P → Location → Bool
  deriving Inhabited
