import Core.Doc.Interp
import Core.Dsl.DefFn
import MIR.Body
import MIR.Place
import MIR.Ty
import PCG.Capability
import PCG.Owned.InitialisationState
import PCG.Owned.InitTree
import PCG.Owned.OwnedLocal
import PCG.PcgData

defFn getAlloc (.plain "getAlloc")
  (.seq [.plain "Look up the owned allocation for a local in \
    an owned state. Returns the ",
    Doc.refLinkOf @InitTree "InitTree", .plain " when the local is in bounds \
    and has been allocated, and ", .code "None",
    .plain " when it is out of bounds or still unallocated."])
  (os "The owned state." : OwnedState)
  (l "The local whose allocation is requested." : Local)
  : Option InitTree :=
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
  (mlp "The maybe-labelled place." : MaybeLabelled Place)
  : Option Place where
  | .current p => Some p
  | .labelled _ _ => None

defFn placeIsMutablyBorrowed (.plain "placeIsMutablyBorrowed")
  (.seq [.plain "Whether the current form of ",
    .math (.raw "p"),
    .plain " is the blocked side of a mutable deref edge in \
      the graph. A deref edge is mutable when its blocked \
      lifetime projection carries a label (the snapshot \
      location at which the mutable reference was taken)."])
  (bg "The borrows graph." : BorrowsGraph Place)
  (p "The target place." : Place)
  : Bool :=
  bg·derefEdges·any fun de =>
    if currentPlace ‹de↦blockedPlace› == Some p then
      de↦blockedLifetimeProjection↦label·isSome
    else false

end BorrowsGraph

-- ══════════════════════════════════════════════
-- Walking an init tree for a place
-- ══════════════════════════════════════════════

defFn treeIsInternal (.plain "treeIsInternal")
  (.seq [.plain "Whether walking an initialisation tree along \
    the given projection ends at an internal (partially \
    initialised) node. A leaf anywhere in the walk returns ",
    .code "false", .plain "; so does a projection step that \
    does not match the tree's expansion shape (the walk leaves \
    the tree)."])
  (projs "The remaining projection elements."
      : List ProjElem)
  (t "The initialisation tree." : InitTree)
  : Bool where
  | _ ; .leaf _ => false
  | [] ; .internal _ => true
  | .deref :: rest ; .internal (.deref sub) =>
      treeIsInternal ‹rest, sub›
  | _ :: _ ; .internal _ => false

defFn treeLeafCapability (.plain "treeLeafCapability")
  (.seq [.plain "The capability implied by the initialisation \
    state of the leaf reached by walking the given projection \
    through an initialisation tree: ",
    .math (.bold (.raw "W")),
    .plain " for an uninitialised leaf, ",
    .math (.bold (.raw "e")),
    .plain " for a shallowly initialised leaf. Fully \
    initialised leaves and walks that end at (or fall off) an \
    internal node return ", .code "None",
    .plain ", deferring to the rest of ", Doc.refLinkByName "getCapability",
    .plain "'s cascade."])
  (projs "The remaining projection elements."
      : List ProjElem)
  (t "The initialisation tree." : InitTree)
  : Option Capability where
  | _ ; .leaf (.uninit) => Some Capability.write
  | _ ; .leaf (.shallow) => Some Capability.shallowExclusive
  | _ ; .leaf (.deep) => None
  | [] ; .internal _ => None
  | .deref :: rest ; .internal (.deref sub) =>
      treeLeafCapability ‹rest, sub›
  | _ :: _ ; .internal _ => None

-- ══════════════════════════════════════════════
-- Prefix-of-read-place check
-- ══════════════════════════════════════════════

defFn isPrefixOf (.plain "isPrefixOf")
  (.plain "Whether one projection is a prefix of another.")
  (l1 "The candidate prefix." : List ProjElem)
  (l2 "The full projection." : List ProjElem)
  : Bool where
  | [] ; _ => true
  | _ :: _ ; [] => false
  | a :: as ; b :: bs =>
      if a == b then isPrefixOf ‹as, bs› else false

defFn isPrefixOfPlace (.plain "isPrefixOfPlace")
  (.plain "Whether one place is a prefix of another: same \
    local and the first's projection is a prefix of the \
    second's.")
  (p "The candidate prefix." : Place)
  (q "The full place." : Place)
  : Bool :=
  if p↦«local» == q↦«local» then
    isPrefixOf ‹p↦projection, q↦projection›
  else false

defFn isPrefixOfReadPlace (.plain "isPrefixOfReadPlace")
  (.plain "Whether a place is a prefix of some place in the \
    read set.")
  (reads "The set of places read at this program point."
      : Set Place)
  (p "The candidate prefix." : Place)
  : Bool :=
  reads·toList·any fun q => isPrefixOfPlace ‹p, q›

defFn isPrefixOfTransientReadPlace
    (.plain "isPrefixOfTransientReadPlace")
  (.seq [.plain "Whether a place is a prefix of some place in \
    the transient read set carried by the optional ",
    Doc.refLinkOf @TransientState "TransientState",
    .plain ". Returns ", .code "false",
    .plain " when the transient place is absent or carries a \
    write-borrowed place rather than a read-place set."])
  (tp "The optional transient place."
      : Option (TransientState Place))
  (p "The candidate prefix." : Place)
  : Bool where
  | .some (.readPlaces reads) ; p =>
      isPrefixOfReadPlace ‹reads, p›
  | _ ; _ => false

-- ══════════════════════════════════════════════
-- Type-directed query: does the place project through
-- a shared-reference dereference?
-- ══════════════════════════════════════════════

defFn projectsSharedRef' (.plain "projectsSharedRef'")
  (.seq [.plain "Walk a projection list against a starting \
    type and report whether any ", .code "*", .plain " step \
    is applied to a shared-reference type. Returns ",
    .code "true", .plain " on the first ",
    .code ".deref", .plain " step taken on a ",
    .code ".ref _ shared _", .plain "; ",
    .code "false",
    .plain " when the projection finishes without one."])
  (τ "The current type." : Ty)
  (projs "The remaining projection elements."
      : List ProjElem)
  requires validProjTy(τ, projs)
  : Bool where
  | _ ; [] => false
  | .ref _ (.shared) _ ; .deref :: _ => true
  | .ref _ _ pointee ; .deref :: π =>
      projectsSharedRef' ‹pointee, π›
  | .box inner ; .deref :: π =>
      projectsSharedRef' ‹inner, π›
  | _ ; (.field _ τ) :: π =>
      projectsSharedRef' ‹τ, π›
  | .array elem _ ; (.index _) :: π =>
      projectsSharedRef' ‹elem, π›
  | τ ; (.downcast _) :: π =>
      projectsSharedRef' ‹τ, π›

defFn projectsSharedRef (.plain "projectsSharedRef")
  (.seq [.plain "Whether the place's projection ever \
    dereferences a shared-reference-typed place: walks the \
    projection from the base local's declared type and \
    reports the first such dereference."])
  (body "The function body." : Body)
  (p "The place." : Place)
  requires validPlace(body, p)
  : Bool :=
    projectsSharedRef'
      ‹body↦decls ! p↦«local»↦index, p↦projection,
        lean_proof("h_validPlace.2")›

-- ══════════════════════════════════════════════
-- Top-level capability lookup
-- ══════════════════════════════════════════════

open BorrowsGraph in
defFn getCapability (.plain "getCapability")
  (.seq [.plain "Compute the capability of a MIR place from \
    the per-program-point PCG data. The cascade: (1) return ",
    .code "None",
    .plain " when the local is not allocated in the owned \
    state, the place lands on an internal node of the init \
    tree, or it is the blocked side of a mutable deref edge, \
    (2) return ",
    .math (.bold (.raw "W")),
    .plain " or ", .math (.bold (.raw "e")),
    .plain " when it is an uninitialised or shallowly \
    initialised leaf in the init tree, (3) return ",
    .math (.bold (.raw "R")),
    .plain " when it projects from a shared reference, (4) \
    return ", .math (.bold (.raw "R")),
    .plain " when it is a prefix of some place in the \
    transient read-place set carried by ",
    .code "transientState", .plain ", otherwise (5) ",
    .math (.bold (.raw "E")), .plain "."])
  (pd "The PCG data." : PcgData Place)
  (body "The function body." : Body)
  (p "The place whose capability is requested." : Place)
  requires validPlace(body, p)
  : Option Capability :=
    let tree ← getAlloc ‹pd↦ownedState, p↦«local»› ;
    let projs := p↦projection ;
    if treeIsInternal ‹projs, tree›
        ∨ placeIsMutablyBorrowed ‹pd↦bg, p›
      then None
    else
      match treeLeafCapability ‹projs, tree› with
      | .some c => Some c
      | .none =>
          if projectsSharedRef ‹body, p, lean_proof("h_validPlace")›
              ∨ isPrefixOfTransientReadPlace ‹pd↦transientState, p›
            then Some Capability.read
          else Some Capability.exclusive
      end
