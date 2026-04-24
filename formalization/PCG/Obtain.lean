import Core.Dsl.DefFn
import MIR.Place
import MIR.Ty
import PCG.Capability
import PCG.Owned.InitTree
import PCG.Owned.InitialisationState
import PCG.Owned.OwnedLocal
import PCG.Owned.OwnedState
import PCG.PcgData
import PCG.PlaceExpansion

-- ══════════════════════════════════════════════
-- Obtain Write on an owned initialisation tree
-- ══════════════════════════════════════════════

defFnMutual
defFn expansionOfStep (.plain "expansionOfStep")
  (.seq [.plain "Build a single-child place expansion that \
    models one projection step taken while unpacking an owned \
    initialisation tree. The caller supplies the subtree to \
    carry as the single child; no sibling children are \
    materialised. Returns ", .code "None",
    .plain " for guided expansions that have no ",
    .code "ProjElem", .plain " counterpart \
    (", .code "constantIndex", .plain " and ",
    .code "subslice", .plain ")."])
  (π "The projection step taken." : ProjElem)
  (child "The subtree to carry as the single child."
      : InitTree)
  : Option (PlaceExpansion InitTree) where
  | .deref ; child =>
      Some (.deref ‹child›)
  | .field fi ty ; child =>
      Some (.fields ‹[⟨fi, ty, child⟩]›)
  | .downcast v ; child =>
      Some (.guided ‹.downcast ‹v, child››)
  | .index l ; child =>
      Some (.guided ‹.index ‹l, child››)
defFn obtainWriteInTree (.plain "obtainWriteInTree")
  (.seq [.plain "Restructure an initialisation tree so that \
    the place reached by the given projection has write (",
    .math (.bold (.raw "W")),
    .plain ") capability, i.e. is marked as uninitialised. \
    Three cases drive the recursion: (1) when the remaining \
    projection is empty, the whole subtree collapses to a \
    single uninitialised leaf — this covers both changing the \
    target leaf to ", .math (.bold (.raw "U")),
    .plain " and packing postfix places back up into a single \
    uninitialised leaf; (2) when the tree is a fully \
    initialised (", .math (.bold (.raw "D")),
    .plain ") leaf and a projection step remains, unpack one \
    level via ", .code "expansionOfStep",
    .plain " and recurse on the single child carrying the \
    same ", .math (.bold (.raw "D")),
    .plain " leaf (the capability dominating the prefix \
    place); (3) when the tree is already internal, descend \
    into the matching child. Shallow (",
    .math (.bold (.raw "S")),
    .plain ") leaves and expansion shapes that do not match \
    the projection step are not handled by the simple case \
    and return ", .code "None", .plain "."])
  (it "The current initialisation subtree." : InitTree)
  (projs "The remaining projection steps from the current \
    subtree down to the target place."
      : List ProjElem)
  : Option InitTree where
  | _ ; [] => Some (.leaf ‹.uninit›)
  | .leaf (.uninit) ; _ :: _ => Some (.leaf ‹.uninit›)
  | .leaf (.deep) ; π :: rest =>
      let child ← obtainWriteInTree ‹.leaf ‹.deep›, rest› ;
      let xp ← expansionOfStep ‹π, child› ;
      Some (.internal ‹xp›)
  | .leaf (.shallow) ; _ :: _ => None
  | .internal (.deref sub) ; .deref :: rest =>
      let newSub ← obtainWriteInTree ‹sub, rest› ;
      Some (.internal ‹.deref ‹newSub››)
  | .internal (.fields fs) ; .field fi _ :: rest =>
      let newFs ← obtainWriteInFields ‹fs, fi, rest› ;
      Some (.internal ‹.fields ‹newFs››)
  | .internal (.guided (.downcast v sub)) ; .downcast v' :: rest =>
      if v == v' then
        let newSub ← obtainWriteInTree ‹sub, rest› ;
        Some (.internal ‹.guided ‹.downcast ‹v, newSub›››)
      else None
  | .internal (.guided (.index l sub)) ; .index l' :: rest =>
      if l == l' then
        let newSub ← obtainWriteInTree ‹sub, rest› ;
        Some (.internal ‹.guided ‹.index ‹l, newSub›››)
      else None
  | .internal _ ; _ :: _ => None
defFn obtainWriteInFields (.plain "obtainWriteInFields")
  (.seq [.plain "Descend into a ", .code "fields",
    .plain " expansion looking for the child with the given \
    field index and recursively obtain write capability on \
    that child along the remaining projection. Returns the \
    updated list of children, preserving the other entries."])
  (fs "The children of the fields expansion."
      : List (FieldIdx × Ty × InitTree))
  (fi "The field index to descend into." : FieldIdx)
  (rest "The remaining projection steps from the chosen \
    child down to the target place."
      : List ProjElem)
  : Option (List (FieldIdx × Ty × InitTree)) where
  | [] ; _ ; _ => None
  | ⟨f, t, sub⟩ :: tail ; fi ; rest =>
      if f == fi then
        let newSub ← obtainWriteInTree ‹sub, rest› ;
        Some (⟨f, t, newSub⟩ :: tail)
      else
        let newTail ← obtainWriteInFields ‹tail, fi, rest› ;
        Some (⟨f, t, sub⟩ :: newTail)
end

-- ══════════════════════════════════════════════
-- Lifting the tree operation to the owned state
-- ══════════════════════════════════════════════

defFn setOwnedLocalAt (.plain "setOwnedLocalAt")
  (.plain "Replace the owned local at a given index in an \
    owned state. Out-of-range indices are left unchanged.")
  (os "The owned state." : OwnedState)
  (idx "The local index to replace." : Nat)
  (newOl "The replacement owned local." : OwnedLocal)
  : OwnedState :=
    OwnedState⟨os↦locals·zipIdx·map fun ⟨ol, i⟩ =>
      if i == idx then newOl else ol⟩

defFn obtainWriteOwned (.plain "obtainWriteOwned")
  (.seq [.plain "Obtain write (",
    .math (.bold (.raw "W")),
    .plain ") capability on an owned place by restructuring \
    its local's initialisation tree. Returns ",
    .code "None",
    .plain " when the local is unallocated or when the tree \
    restructuring fails (unsupported shape, shallow leaf on \
    the path, etc.)."])
  (os "The owned state." : OwnedState)
  (p "The place to obtain." : Place)
  : Option OwnedState :=
    let ol ← os↦locals !! p↦base↦index ;
    match ol with
    | .allocated it =>
        let newIt ← obtainWriteInTree ‹it, p↦projection› ;
        Some (setOwnedLocalAt ‹os, p↦base↦index, .allocated ‹newIt››)
    | .unallocated => None
    end

-- ══════════════════════════════════════════════
-- Top-level obtain on PCG data
-- ══════════════════════════════════════════════

namespace PcgData

defFn obtain (.plain "obtain")
  (.seq [.plain "Restructure the PCG so that the given place \
    holds the given capability. Only the simple case of \
    obtaining write (", .math (.bold (.raw "W")),
    .plain ") capability on an owned place is handled: the \
    borrows graph, basic block, and read places are left \
    untouched and only the owned state is updated via ",
    .code "obtainWriteOwned", .plain ". Other capabilities \
    return ", .code "None", .plain "."])
  (pd "The PCG data." : PcgData Place)
  (p "The place to obtain." : Place)
  (c "The capability to obtain." : Capability)
  : Option (PcgData Place) where
  | pd ; p ; .write =>
      let newOs ← obtainWriteOwned ‹pd↦ownedState, p› ;
      Some (PcgData⟨pd↦bg, newOs, pd↦basicBlock,
              pd↦transientState⟩)
  | _ ; _ ; _ => None

end PcgData
