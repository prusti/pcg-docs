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
-- Borrow-state helpers (plain Lean)
-- ══════════════════════════════════════════════

namespace BorrowsGraph

/-- Every `DerefEdge` recorded in the graph. -/
def derefEdges (bg : BorrowsGraph Place) : List (DerefEdge Place) :=
  bg.edges.toList.filterMap fun (e, _) =>
    match e with
    | .deref de => some de
    | _ => none

/-- The current (unlabelled) MIR place at the source of a
    `MaybeLabelledPlace`, when it has one. -/
private def currentPlace : MaybeLabelledPlace Place → Option Place
  | .current p => some p
  | .labelled _ _ => none

/-- The deref edges whose `derefPlace` is the current
    (unlabelled) form of `p`. -/
def derefEdgesTo (bg : BorrowsGraph Place) (p : Place)
    : List (DerefEdge Place) :=
  bg.derefEdges.filter fun de =>
    currentPlace de.derefPlace == some p

/-- Whether some deref edge ending at `p` blocks a *shared*
    reference. We use the documented convention on
    `DerefEdge.blockedLifetimeProjection`: an unlabelled
    projection corresponds to a shared borrow, a labelled one
    to a mutable borrow. -/
def projectsSharedBorrow
    (bg : BorrowsGraph Place) (p : Place) : Bool :=
  (bg.derefEdgesTo p).any fun de =>
    de.blockedLifetimeProjection.label.isNone

/-- Whether the current-form of `p` appears as the *blocked*
    side of any edge in the graph. Used as a coarse proxy for
    "`p` has a non-trivial out-edge in the borrow PCG". Only
    deref-edge blockers are considered for now; refining this
    to cover the other edge kinds is a follow-up. -/
def placeIsBlocked
    (bg : BorrowsGraph Place) (p : Place) : Bool :=
  bg.derefEdges.any fun de =>
    currentPlace de.blockedPlace == some p

/-- Whether `p` is a leaf in the borrow PCG: it appears as a
    deref target somewhere in the graph and is not itself
    blocked by another edge. -/
def placeIsBorrowLeaf
    (bg : BorrowsGraph Place) (p : Place) : Bool :=
  !(bg.derefEdgesTo p).isEmpty && !bg.placeIsBlocked p

end BorrowsGraph

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
    if BorrowsGraph.projectsSharedBorrow ‹bg, p› then
      Capability.read
    else if BorrowsGraph.placeIsBorrowLeaf ‹bg, p› then
      Capability.exclusive
    else
      Capability.none

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
      | .none => borrowedPlaceCapability ‹pd↦bg, p›
      | c => c
      end
