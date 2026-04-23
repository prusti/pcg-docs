import Core.Dsl.DefStruct
import MIR.Body
import PCG.BorrowsGraph
import PCG.Owned.OwnedState

defStruct PcgData {P}
    (.doc (.plain "pd"), .doc (.plain "PcgData"))
  "PCG Data"
  (.seq [
    .plain "The PCG data ",
    Doc.defMath (.doc (.plain "pd"))
      (.doc (.plain "PcgData")) ["P"],
    .plain " bundles the per-program-point state tracked by \
     the PCG: the borrows graph, the owned state, the current \
     basic block, and the set of places read at this point."])
where
  | bg "The borrows portion of the PCG."
      : BorrowsGraph P
  | ownedState "The owned portion of the PCG."
      : OwnedState
  | basicBlock "The current basic block."
      : BasicBlockIdx
  | readPlaces "The places read at this program point."
      : Set P
  deriving Repr
