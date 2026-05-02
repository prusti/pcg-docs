import MIR.Body
import PCG.Nodes.PcgNode

defStruct BorrowChecker {P}
    (.text "bc",
     .text "BorrowChecker")
  "BorrowCheckers"
  (.seq [
    .plain "A borrow-checker ",
    .math (.seq [.text "bc", .sym .setContains, .text "BorrowChecker", .sym .space, .raw "P"]),
    .plain " is an oracle that exposes the subset of \
     Polonius-style facts needed by the PCG: for each PCG \
     node and MIR location, whether the node is live at \
     that location."])
where
  | isLive "Liveness predicate."
      : PcgNode P → Location → Bool
  deriving Inhabited
