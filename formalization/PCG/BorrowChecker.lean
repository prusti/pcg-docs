import MIR.Body
import PCG.Nodes.PcgNode

defStruct BorrowChecker {P}
    (.text "bc",
     .text "BorrowChecker")
  "BorrowCheckers"
  (doc! "A borrow-checker \
    $_bc_ ∈ _BorrowChecker_ _P_$ \
    is an oracle that exposes the subset of Polonius-style \
    facts needed by the PCG: for each PCG node and MIR \
    location, whether the node is live at that location.")
where
  | isLive "Liveness predicate."
      : PcgNode P → Location → Bool
  deriving Inhabited
