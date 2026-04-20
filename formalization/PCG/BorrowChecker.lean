import MIR.Body
import PCG.PcgNode

defStruct BorrowChecker {P}
    (.doc (.plain "bc"),
     .doc (.plain "BorrowChecker"))
  "BorrowCheckers"
  (.seq [
    .plain "A borrow-checker ",
    Doc.defMath (.doc (.plain "bc"))
      (.doc (.plain "BorrowChecker")),
    .plain " is an oracle that exposes the subset of \
     Polonius-style facts needed by the PCG: for each PCG \
     node and MIR location, whether the node is live at \
     that location."])
where
  | isLive "Liveness predicate."
      : PcgNode P → Location → Bool
  deriving Inhabited
