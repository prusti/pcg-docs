import Core.Dsl.DefFn
import MIR.Body
import MIR.Place
import PCG.Capability
import PCG.Obtain.Owned
import PCG.PcgData
import PCG.TransientState

-- ══════════════════════════════════════════════
-- Top-level obtain on PCG data
-- ══════════════════════════════════════════════

namespace PcgData

defFn obtain (.plain "obtain")
  (doc! "Restructure the PCG so that the given place holds \
    the given capability. Three cases are currently handled. \
    (1) Write ($__W__$) on a place that projects through a \
    reference (i.e. #isOwned is `false`): leave the borrows \
    graph and owned state untouched and stash the place in \
    `transientState` as a #TransientState.writeBorrowedPlace \
    — the borrow's expiry is what will eventually surrender \
    the write capability. (2) Write on an owned place: \
    restructure the owned state's initialisation tree via \
    #obtainWriteOwned. (3) Read ($__R__$) on any place \
    (owned or borrowed): add the place to the transient \
    read-place set. `transientState` moves from `None` to a \
    fresh #TransientState.readPlaces holding the singleton \
    set containing the place, or extends the existing \
    read-place set; an existing \
    #TransientState.writeBorrowedPlace is incompatible with \
    a read obtain and yields `None`. Other capabilities \
    return `None`.")
  (pd "The PCG data." : PcgData Place)
  (body "The function body." : Body)
  (p "The place to obtain." : Place)
  (c "The capability to obtain." : Capability)
  requires validPlace(body, p)
  : Option (PcgData Place) where
  | pd ; body ; p ; .write =>
      if isOwned ‹body, p, proof[h_validPlace]› then
        let newOs ← obtainWriteOwned ‹pd↦os, p› ;
        Some pd[os => newOs]
      else
        Some pd[transientState =>
          Some (.writeBorrowedPlace ‹p›)]
  | pd ; _ ; p ; .read =>
      match pd↦transientState with
      | .none =>
          Some pd[transientState => Some (.readPlaces ‹⦃p⦄›)]
      | .some (.readPlaces s) =>
          Some pd[transientState =>
            Some (.readPlaces ‹s ∪ ⦃p⦄›)]
      | .some (.writeBorrowedPlace _) => None
      end
  | _ ; _ ; _ ; _ => None

end PcgData
