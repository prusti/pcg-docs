import Core.Dsl.DefFn
import Core.Dsl.DefStruct
import MIR.Body
import PCG.BorrowsGraph
import PCG.Edges.PcgEdge
import PCG.Edges.UnpackEdge
import PCG.Nodes.PcgNode
import PCG.Owned.InitTree
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

-- ══════════════════════════════════════════════
-- Converting owned init trees to unpack edges
-- ══════════════════════════════════════════════

defFn placeNode (.plain "placeNode")
  (.plain "Wrap a MIR place as a PCG node: inject it as a \
    current (unlabelled) maybe-labelled place nested inside a \
    PCG place and then a PCG node.")
  (p "The place to wrap." : Place)
  : PcgNode Place :=
    PcgNode.place
      ‹PcgPlace.maybeLabelled
        ‹MaybeLabelledPlace.current ‹p›››

defFnMutual
defFn itUnpackEdges (.plain "itUnpackEdges")
  (.seq [.plain "All unpack edges derived from walking an \
    initialisation tree from a base local along an accumulated \
    projection. Each internal node contributes one unpack edge \
    from the node's place to the list of its children's places; \
    leaves contribute no edges."])
  (it "The initialisation tree." : InitTree)
  (base "The base local the tree is rooted at." : Local)
  (projAcc "The projection accumulated so far, from the root."
      : List ProjElem)
  : List (UnpackEdge (PcgNode Place)) where
  | .leaf _ ; _ ; _ => []
  | .internal (.fields fs) ; base ; projAcc =>
      let self :=
        UnpackEdge⟨
          placeNode ‹Place⟨base, projAcc⟩›,
          fs·map fun ⟨fi, ty, _⟩ =>
            placeNode
              ‹Place⟨base,
                projAcc ++ [ProjElem.field ‹fi, ty›]⟩›⟩ ;
      self :: fieldsSubedges ‹fs, base, projAcc›
  | .internal (.deref d) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.deref] ;
      let self :=
        UnpackEdge⟨
          placeNode ‹Place⟨base, projAcc⟩›,
          [placeNode ‹Place⟨base, proj⟩›]⟩ ;
      self :: itUnpackEdges ‹d, base, proj›
  | .internal (.guided (.downcast v d)) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.downcast ‹v›] ;
      let self :=
        UnpackEdge⟨
          placeNode ‹Place⟨base, projAcc⟩›,
          [placeNode ‹Place⟨base, proj⟩›]⟩ ;
      self :: itUnpackEdges ‹d, base, proj›
  | .internal (.guided (.constantIndex _ d)) ; base ; projAcc =>
      itUnpackEdges ‹d, base, projAcc›
  | .internal (.guided (.index l d)) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.index ‹l›] ;
      let self :=
        UnpackEdge⟨
          placeNode ‹Place⟨base, projAcc⟩›,
          [placeNode ‹Place⟨base, proj⟩›]⟩ ;
      self :: itUnpackEdges ‹d, base, proj›
  | .internal (.guided (.subslice _ _ _ d)) ; base ; projAcc =>
      itUnpackEdges ‹d, base, projAcc›
defFn fieldsSubedges (.plain "fieldsSubedges")
  (.seq [.plain "Helper for ", .code "itUnpackEdges",
    .plain ": accumulate unpack edges from every child of a \
    fields expansion, prefixing each child's path with its \
    field step."])
  (fs "Children of a fields expansion."
      : List (FieldIdx × Ty × InitTree))
  (base "The base local the tree is rooted at." : Local)
  (projAcc "The projection accumulated so far, from the root."
      : List ProjElem)
  : List (UnpackEdge (PcgNode Place)) where
  | [] ; _ ; _ => []
  | ⟨fi, ty, sub⟩ :: rest ; base ; projAcc =>
      itUnpackEdges ‹sub, base,
        projAcc ++ [ProjElem.field ‹fi, ty›]›
      ++ fieldsSubedges ‹rest, base, projAcc›
end

defFn localsUnpackEdges (.plain "localsUnpackEdges")
  (.seq [.plain "Walk a list of owned locals, starting at the \
    given local index, and collect every unpack edge derived \
    from each allocated local's initialisation tree. \
    Unallocated slots contribute no edges but still consume an \
    index slot."])
  (locals "The remaining owned locals to walk."
      : List OwnedLocal)
  (idx "The local index corresponding to the head of the list."
      : Nat)
  : List (UnpackEdge (PcgNode Place)) where
  | [] ; _ => []
  | .unallocated :: rest ; idx =>
      localsUnpackEdges ‹rest, idx + 1›
  | .allocated it :: rest ; idx =>
      itUnpackEdges ‹it, Local⟨idx⟩, []›
      ++ localsUnpackEdges ‹rest, idx + 1›

defFn edges (.plain "edges")
  (.seq [.plain "All PCG hyperedges represented by the per-\
    program-point PCG data. Combines the unpack edges derived \
    from the internal structure of each allocated owned \
    initialisation tree with every edge recorded in the \
    borrows graph. Unpack edges needed to materialise the \
    tree further (to cover ", .code "readPlaces",
    .plain " or owned deref-edge sources that extend beyond \
    the current tree shape) are a follow-up."])
  (pd "The PCG data." : PcgData Place)
  : List (PcgEdge Place) :=
    (localsUnpackEdges ‹pd↦ownedState↦locals, 0›
      ·map fun ue => PcgEdge.unpack ‹ue›)
    ++ (pd↦bg↦edges·toList·map fun ⟨e, _⟩ => e)
