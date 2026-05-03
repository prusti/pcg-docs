import Core.Dsl.DefFn
import MIR.Place
import MIR.Ty
import PCG.Owned.InitTree
import PCG.Owned.InitialisationState
import PCG.PlaceExpansion

-- ══════════════════════════════════════════════
-- Obtain Write on an owned initialisation tree
-- ══════════════════════════════════════════════

defFn expansionOfStep (.plain "expansionOfStep")
  (doc! "Build a single-child place expansion that models one projection step taken while unpacking \
    an owned initialisation tree. The caller supplies the subtree to carry as the single child; no \
    sibling children are materialised. Total on #ProjElem: every projection step has a unique \
    single-child expansion shape (the `constantIndex` and `subslice` guided variants have no \
    #ProjElem counterpart and so cannot arise here).")
  (π "The projection step taken." : ProjElem)
  (child "The subtree to carry as the single child."
      : InitTree)
  : PlaceExpansion InitTree where
  | .deref ; child =>
      .deref child
  | .field fi ty ; child =>
      .fields [⟨fi, ty, child⟩]
  | .downcast v ; child =>
      .guided (.downcast v child)
  | .index l ; child =>
      .guided (.index l child)

defFnMutual
defFn obtainWriteInTree (.plain "obtainWriteInTree")
  (doc! "Restructure an initialisation tree so that the place \
    reached by the given projection has write ($__W__$) \
    capability, i.e. is marked as uninitialised. Three cases \
    drive the recursion: (1) when the remaining projection is \
    empty, the whole subtree collapses to a single \
    uninitialised leaf — this covers both changing the target \
    leaf to $__U__$ and packing postfix places back up into a \
    single uninitialised leaf; (2) when the tree is a fully \
    initialised ($__D__$) leaf and a projection step remains, \
    unpack one level via #expansionOfStep and recurse on the \
    single child carrying the same $__D__$ leaf (the \
    capability dominating the prefix place); (3) when the \
    tree is already internal, descend into the matching \
    child. Shallow ($__S__$) leaves and expansion shapes that \
    do not match the projection step are not handled by the \
    simple case and return `None`.")
  (it "The current initialisation subtree." : InitTree)
  (projs "The remaining projection steps from the current \
    subtree down to the target place."
      : List ProjElem)
  : Option InitTree where
  | _ ; [] => Some (.leaf .uninit)
  | .leaf (.uninit) ; _ :: _ => Some (.leaf .uninit)
  | .leaf (.deep) ; π :: rest =>
      let child ← obtainWriteInTree (.leaf .deep) rest ;
      Some (.internal (expansionOfStep π child))
  | .leaf (.shallow) ; _ :: _ => None
  | .internal (.deref sub) ; .deref :: rest =>
      let newSub ← obtainWriteInTree sub rest ;
      Some (.internal (.deref newSub))
  | .internal (.fields fs) ; .field fi _ :: rest =>
      let newFs ← obtainWriteInFields fs fi rest ;
      Some (.internal (.fields newFs))
  | .internal (.guided (.downcast v sub)) ; .downcast v' :: rest =>
      if v == v' then
        let newSub ← obtainWriteInTree sub rest ;
        Some (.internal (.guided (.downcast v newSub)))
      else None
  | .internal (.guided (.index l sub)) ; .index l' :: rest =>
      if l == l' then
        let newSub ← obtainWriteInTree sub rest ;
        Some (.internal (.guided (.index l newSub)))
      else None
  | .internal _ ; _ :: _ => None
defFn obtainWriteInFields (.plain "obtainWriteInFields")
  (doc! "Descend into a `fields` expansion looking for the child with the given field index and \
    recursively obtain write capability on that child along the remaining projection. Returns the \
    updated list of children, preserving the other entries.")
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
        let newSub ← obtainWriteInTree sub rest ;
        Some (⟨f, t, newSub⟩ :: tail)
      else
        let newTail ← obtainWriteInFields tail fi rest ;
        Some (⟨f, t, sub⟩ :: newTail)
end
