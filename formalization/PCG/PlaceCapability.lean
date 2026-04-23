import Core.Dsl.DefFn
import MIR.Place
import PCG.Capability
import PCG.Owned.InitialisationState
import PCG.Owned.InitTree
import PCG.Owned.OwnedLocal
import PCG.PcgData

defFn initStateCapability (.plain "initStateCapability")
  (.seq [.plain "Translate an initialisation state into the \
    place capability implied by that state in isolation \
    (without consulting the borrow state). See ",
    .code "computing-place-capabilities.md", .plain "."])
  (i "The initialisation state." : InitialisationState)
  : Capability where
  | .uninit => Capability.write
  | .shallow => Capability.shallowExclusive
  | .deep => Capability.exclusive

defFn treeCapability (.plain "treeCapability")
  (.seq [.plain "Walk an initialisation tree along a place \
    projection and return the implied capability. A leaf \
    determines the capability of every descendant place via ",
    .code "initStateCapability", .plain ". An internal node \
    reached with no remaining projection is partially \
    initialised, so the capability is ", .math (.sym .emptySet),
    .plain ". This function conservatively returns ",
    .math (.sym .emptySet),
    .plain " at any tree/projection mismatch; a follow-up \
    will walk struct/tuple and guided expansions exactly."])
  (projs "The remaining projection elements."
      : List ProjElem)
  (t "The initialisation tree." : InitTree)
  : Capability where
  | _ ; .leaf i => initStateCapability ‹i›
  | [] ; .internal _ => Capability.none
  | .deref :: rest ; .internal (.deref sub) =>
      treeCapability ‹rest, sub›
  | _ :: _ ; .internal _ => Capability.none

defFn getCapability (.plain "getCapability")
  (.seq [.plain "Compute the capability of a MIR place from \
    the per-program-point PCG data, following ",
    .code "computing-place-capabilities.md",
    .plain ". This implementation covers the owned-state \
    lookup; borrow-state adjustments will be added \
    incrementally."])
  (pd "The PCG data." : PcgData Place)
  (p "The place whose capability is requested." : Place)
  : Capability where
  | pd ; p =>
      match pd↦ownedState↦locals !! p↦base↦index with
      | .some (.allocated t) =>
          treeCapability ‹p↦projection, t›
      | _ => Capability.none
      end
