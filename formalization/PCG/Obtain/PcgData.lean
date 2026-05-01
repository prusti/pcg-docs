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
  (.seq [.plain "Restructure the PCG so that the given place \
    holds the given capability. Three cases are currently \
    handled. (1) Write (", .math (.bold (.raw "W")),
    .plain ") on a place that projects through a reference \
    (i.e. ", Doc.refLinkOf @isOwned "isOwned", .plain " is ", .code "false",
    .plain "): leave the borrows graph and owned state \
    untouched and stash the place in ",
    .code "transientState", .plain " as a ",
    Doc.refLinkOf @TransientState.writeBorrowedPlace "TransientState.writeBorrowedPlace",
    .plain " — the borrow's expiry is what will eventually \
    surrender the write capability. (2) Write on an owned \
    place: restructure the owned state's initialisation \
    tree via ", Doc.refLinkOf @obtainWriteOwned "obtainWriteOwned",
    .plain ". (3) Read (", .math (.bold (.raw "R")),
    .plain ") on any place (owned or borrowed): add the \
    place to the transient read-place set. ",
    .code "transientState", .plain " moves from ",
    .code "None", .plain " to ",
    .code "Some (TransientState.readPlaces {p})",
    .plain " or extends the existing read-place set; an \
    existing ", Doc.refLinkOf @TransientState.writeBorrowedPlace "TransientState.writeBorrowedPlace",
    .plain " is incompatible with a read obtain and yields ",
    .code "None", .plain ". Other capabilities return ",
    .code "None", .plain "."])
  (pd "The PCG data." : PcgData Place)
  (body "The function body." : Body)
  (p "The place to obtain." : Place)
  (c "The capability to obtain." : Capability)
  requires validPlace(body, p)
  : Option (PcgData Place) where
  | pd ; body ; p ; .write =>
      if isOwned ‹body, p, lean_proof("h_validPlace")› then
        let newOs ← obtainWriteOwned ‹pd↦ownedState, p› ;
        Some pd[ownedState => newOs]
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
