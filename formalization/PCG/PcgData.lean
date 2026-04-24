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
-- Borrow-graph helpers used by the edge extractor
-- ══════════════════════════════════════════════

namespace BorrowsGraph

defFn blockedCurrentPlaces (.plain "blockedCurrentPlaces")
  (.seq [.plain "The current (unlabelled) blocked places \
    appearing as the source of a deref edge in the graph. \
    Labelled blocked places are skipped; the remaining \
    places are the candidates for the owned places that \
    the materialised tree should expose."])
  (bg "The borrows graph." : BorrowsGraph Place)
  : List Place :=
  bg↦edges·toList·flatMap fun ⟨e, _⟩ =>
    match e with
    | .deref de =>
        match de↦blockedPlace with
        | .current p => [p]
        | .labelled _ _ => []
        end
    | _ => []
    end

end BorrowsGraph

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
      let basePlace := placeNode ‹Place⟨base, projAcc⟩› ;
      let children := fs·map fun ⟨fi, ty, _⟩ =>
        let step := ProjElem.field ‹fi, ty› ;
        placeNode ‹Place⟨base, projAcc ++ [step]⟩› ;
      let self := UnpackEdge⟨basePlace, children⟩ ;
      self :: fieldsSubedges ‹fs, base, projAcc›
  | .internal (.deref d) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.deref] ;
      let basePlace := placeNode ‹Place⟨base, projAcc⟩› ;
      let childPlace := placeNode ‹Place⟨base, proj⟩› ;
      let self := UnpackEdge⟨basePlace, [childPlace]⟩ ;
      self :: itUnpackEdges ‹d, base, proj›
  | .internal (.guided (.downcast v d)) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.downcast ‹v›] ;
      let basePlace := placeNode ‹Place⟨base, projAcc⟩› ;
      let childPlace := placeNode ‹Place⟨base, proj⟩› ;
      let self := UnpackEdge⟨basePlace, [childPlace]⟩ ;
      self :: itUnpackEdges ‹d, base, proj›
  | .internal (.guided (.constantIndex _ d)) ; base ; projAcc =>
      itUnpackEdges ‹d, base, projAcc›
  | .internal (.guided (.index l d)) ; base ; projAcc =>
      let proj := projAcc ++ [ProjElem.index ‹l›] ;
      let basePlace := placeNode ‹Place⟨base, projAcc⟩› ;
      let childPlace := placeNode ‹Place⟨base, proj⟩› ;
      let self := UnpackEdge⟨basePlace, [childPlace]⟩ ;
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
      let step := ProjElem.field ‹fi, ty› ;
      let subEdges := itUnpackEdges ‹sub, base, projAcc ++ [step]› ;
      subEdges ++ fieldsSubedges ‹rest, base, projAcc›
end

-- ══════════════════════════════════════════════
-- Materialising the tree up to target places
-- ══════════════════════════════════════════════

defFn projUnpackChain (.plain "projUnpackChain")
  (.seq [.plain "Emit single-child unpack edges walking a \
    remaining projection one step at a time from a base local. \
    Used to materialise the owned part of the PCG beyond the \
    existing init-tree shape so that each target place becomes \
    reachable via an unbroken chain of unpack edges. Because \
    sibling places at each synthetic step are unknown without \
    type information, the expansion of every emitted edge \
    contains just the single child that extends the prefix."])
  (base "The base local the chain is rooted at." : Local)
  (projAcc "The projection covered so far." : List ProjElem)
  (remaining "The projection steps still to walk."
      : List ProjElem)
  : List (UnpackEdge (PcgNode Place)) where
  | _ ; _ ; [] => []
  | base ; projAcc ; π :: rest =>
      let projExt := projAcc ++ [π] ;
      let basePlace := placeNode ‹Place⟨base, projAcc⟩› ;
      let childPlace := placeNode ‹Place⟨base, projExt⟩› ;
      let self := UnpackEdge⟨basePlace, [childPlace]⟩ ;
      self :: projUnpackChain ‹base, projExt, rest›

defFn placeUnpackChain (.plain "placeUnpackChain")
  (.plain "Emit a chain of single-child unpack edges from a \
    place's base local to the place itself, one edge per \
    projection step.")
  (p "The target place." : Place)
  : List (UnpackEdge (PcgNode Place)) :=
  projUnpackChain ‹p↦base, [], p↦projection›

defFn localsUnpackEdges (.plain "localsUnpackEdges")
  (.seq [.plain "For every allocated local in an owned state, \
    collect the unpack edges derived from that local's \
    initialisation tree. Unallocated slots contribute nothing. \
    The local index carried by each entry is recovered from the \
    list position via ", .code "zipIdx", .plain "."])
  (locals "The owned locals to walk." : List OwnedLocal)
  : List (UnpackEdge (PcgNode Place)) :=
    locals·zipIdx·flatMap fun ⟨ol, idx⟩ =>
      match ol with
      | .allocated it => itUnpackEdges ‹it, Local⟨idx⟩, []›
      | .unallocated => []
      end

-- ══════════════════════════════════════════════
-- Collecting all edges represented by PcgData
-- ══════════════════════════════════════════════

namespace PcgData

defFn join (.plain "join")
  (.seq [
    .plain "Join two PCG data values at the program-point \
     entry of basic block ", .code "bb",
    .plain ": pointwise-join the borrows graphs and the \
     owned states (per-local, via ", .code "OwnedState.join",
    .plain "), tag the result with ", .code "bb",
    .plain " as its current basic block, and reset ",
    .code "readPlaces", .plain " to the empty set — read \
    places are local to a single program point and do not \
    propagate across joins."])
  (pd1 "The first PCG data." : PcgData Place)
  (pd2 "The second PCG data." : PcgData Place)
  (bb "The basic block of the joined program point."
      : BasicBlockIdx)
  : PcgData Place :=
    PcgData⟨
      BorrowsGraph.join ‹pd1↦bg, pd2↦bg›,
      OwnedState.join ‹pd1↦ownedState, pd2↦ownedState›,
      bb,
      ∅⟩

end PcgData

defFn edges (.plain "edges")
  (.seq [.plain "All PCG hyperedges represented by the per-\
    program-point PCG data. The result is the union of three \
    sources: (1) unpack edges derived from the internal \
    structure of each allocated owned init tree, (2) unpack \
    edges materialising the tree further to reach every place \
    in ", .code "readPlaces",
    .plain " and every owned place blocked by a deref edge, \
    and (3) every edge already recorded in the borrows graph."])
  (pd "The PCG data." : PcgData Place)
  : List (PcgEdge Place) :=
    let treeEdges := localsUnpackEdges ‹pd↦ownedState↦locals› ;
    let targets := pd↦readPlaces·toList
      ++ BorrowsGraph.blockedCurrentPlaces ‹pd↦bg› ;
    let matEdges := targets·flatMap fun p => placeUnpackChain ‹p› ;
    let unpackEdges := (treeEdges ++ matEdges)
      ·map fun ue => PcgEdge.unpack ‹ue› ;
    unpackEdges ++ pd↦bg↦edges·toList·map fun ⟨e, _⟩ => e
