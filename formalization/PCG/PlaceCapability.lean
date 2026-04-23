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

defFn getAlloc (.plain "getAlloc")
  (.seq [.plain "Look up the owned allocation for a local in \
    an owned state. Returns the ",
    .code "InitTree", .plain " when the local is in bounds \
    and has been allocated, and ", .code "None",
    .plain " when it is out of bounds or still unallocated."])
  (os "The owned state." : OwnedState)
  (l "The local whose allocation is requested." : Local)
  : Option InitTree where
  | os ; l =>
      let ol ← os↦locals !! l↦index ;
      match ol with
      | .allocated t => Some t
      | _ => None
      end

-- ══════════════════════════════════════════════
-- Borrow-state helpers
-- ══════════════════════════════════════════════

namespace BorrowsGraph

defFn derefEdges (.plain "derefEdges")
  (.plain "Every deref edge recorded in the graph.")
  (bg "The borrows graph." : BorrowsGraph Place)
  : List (DerefEdge Place) :=
  bg↦edges·toList·flatMap fun ⟨e, _⟩ =>
    match e with
    | .deref de => [de]
    | _ => []
    end

defFn currentPlace (.plain "currentPlace")
  (.plain "The current (unlabelled) MIR place at the source of \
    a maybe-labelled place, when it has one.")
  (mlp "The maybe-labelled place." : MaybeLabelledPlace Place)
  : Option Place where
  | .current p => Some p
  | .labelled _ _ => None

defFn derefEdgesTo (.plain "derefEdgesTo")
  (.plain "The deref edges whose deref target is the current \
    (unlabelled) form of the given place.")
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The target place." : Place)
  : List (DerefEdge Place) :=
  bg·derefEdges·flatMap fun de =>
    if currentPlace ‹de↦derefPlace› == Some p then [de] else []

defFn projectsSharedBorrow (.plain "projectsSharedBorrow")
  (.seq [.plain "Whether some deref edge ending at ",
    .math (.raw "p"),
    .plain " blocks a shared reference. Uses the convention on ",
    .code "DerefEdge.blockedLifetimeProjection",
    .plain ": an unlabelled projection corresponds to a shared \
      borrow, a labelled one to a mutable borrow."])
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The target place." : Place)
  : Bool :=
  derefEdgesTo ‹bg, p›·any fun de =>
    de↦blockedLifetimeProjection↦label·isNone

defFn placeIsBlocked (.plain "placeIsBlocked")
  (.seq [.plain "Whether the current form of ",
    .math (.raw "p"),
    .plain " appears as the blocked side of any edge in the \
      graph. Used as a coarse proxy for \"",
    .math (.raw "p"),
    .plain " has a non-trivial out-edge in the borrow PCG\". \
      Only deref-edge blockers are considered for now; \
      refining this to cover the other edge kinds is a \
      follow-up."])
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The target place." : Place)
  : Bool :=
  bg·derefEdges·any fun de =>
    currentPlace ‹de↦blockedPlace› == Some p

defFn placeIsBorrowLeaf (.plain "placeIsBorrowLeaf")
  (.seq [.plain "Whether ", .math (.raw "p"),
    .plain " is a leaf in the borrow PCG: it appears as a \
      deref target somewhere in the graph and is not itself \
      blocked by another edge."])
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The target place." : Place)
  : Bool :=
  match derefEdgesTo ‹bg, p› with
  | [] => false
  | _ :: _ => placeIsBlocked ‹bg, p› == false
  end

defFn borrowedPlaceCapability
  (.plain "borrowedPlaceCapability")
  (.seq [.plain "Compute the capability of a place that is \
    not tracked by the owned state but lives in the borrow \
    PCG, following the \"Computing Capabilities for Borrowed \
    Places\" rules in ",
    .code "computing-place-capabilities.md",
    .plain ". Returns ", .math (.bold (.raw "R")),
    .plain " when the place is reached through a shared \
    borrow, ", .math (.bold (.raw "E")),
    .plain " when it is a leaf in the borrow PCG, and ",
    .math (.sym .emptySet),
    .plain " otherwise. The shared/mutable distinction relies \
    on the labelling convention on a deref edge's blocked \
    lifetime projection (unlabelled = shared, labelled = \
    mutable); a precise check using the place's reference \
    type is left as a follow-up."])
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The place whose capability is requested." : Place)
  : Capability :=
    if projectsSharedBorrow ‹bg, p› then
      Capability.read
    else if placeIsBorrowLeaf ‹bg, p› then
      Capability.exclusive
    else
      Capability.none

end BorrowsGraph

defFn getCapability (.plain "getCapability")
  (.seq [.plain "Compute the capability of a MIR place from \
    the per-program-point PCG data, following ",
    .code "computing-place-capabilities.md",
    .plain ". The owned-state lookup runs first; when it \
    yields no capability (the local is unallocated, or the \
    projection takes us off the owned init tree — typically \
    because the place is reached through a non-Box \
    reference), the borrow state is consulted via ",
    .code "borrowedPlaceCapability", .plain "."])
  (pd "The PCG data." : PcgData Place)
  (body "Body" : Body)
  (p "The place whose capability is requested." : Place)
  : Option Capability where
  | pd ; body; p =>
      let t ← getAlloc ‹pd↦ownedState, p↦base› ;
      match treeCapability ‹p↦projection, t› with
      | .none => BorrowsGraph.borrowedPlaceCapability ‹pd↦bg, p›
      | c => c
      end
