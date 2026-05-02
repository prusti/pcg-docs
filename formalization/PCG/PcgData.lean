import Core.Dsl.DefFn
import Core.Dsl.DefStruct
import MIR.Body
import PCG.BorrowsGraph
import PCG.Edges.PcgEdge
import PCG.Edges.UnpackEdge
import PCG.Nodes.PcgNode
import PCG.Owned.InitTree
import PCG.Owned.OwnedState
import PCG.TransientState

defStruct PcgData {P}
    (.text "pd", .text "PcgData")
  "PCG Data"
  (doc! "The PCG data \
    {.math (.seq [(.text "pd"), .sym .setContains, (.text "PcgData"), .sym .space, .raw "P"])} \
    bundles the per-program-point state tracked by the PCG: \
    the borrows graph, the owned state, the current basic \
    block, and an optional #TransientState carrying either \
    the set of places read at this point or a single \
    write-borrowed place.")
where
  | bg "The borrows portion of the PCG."
      : BorrowsGraph P
  | os "The owned portion of the PCG."
      : OwnedState
  | basicBlock "The current basic block."
      : BasicBlockIdx
  | transientState "Transient read- or write-borrow side \
      condition for this program point."
      : Option (TransientState P)
  deriving Repr

-- ══════════════════════════════════════════════
-- Borrow-graph helpers used by the edge extractor
-- ══════════════════════════════════════════════

namespace BorrowsGraph

defFn blockedCurrentPlaces (.plain "blockedCurrentPlaces")
  (doc! "The current (unlabelled) blocked places appearing as the source of a deref edge in the \
    graph. Labelled blocked places are skipped; the remaining places are the candidates for the \
    owned places that the materialised tree should expose.")
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

defFn implicit placeNode (.plain "placeNode")
  (.plain "Wrap a MIR place as a PCG node: inject it as a \
    current (unlabelled) maybe-labelled place nested inside a \
    PCG place and then a PCG node.")
  (p "The place to wrap." : Place)
  : PcgNode Place :=
    PcgNode.place
      ‹PcgPlace.maybeLabelled
        ‹MaybeLabelled.current ‹p›››

defFnMutual
defFn itUnpackEdges (.plain "itUnpackEdges")
  (doc! "All unpack edges derived from walking an initialisation tree from a base local along an \
    accumulated projection. Each internal node contributes one unpack edge from the node's place to \
    the list of its children's places; leaves contribute no edges.")
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
  (doc! "Helper for #itUnpackEdges: accumulate unpack edges from every child of a fields expansion, \
    prefixing each child's path with its field step.")
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
  (doc! "Emit single-child unpack edges walking a remaining projection one step at a time from a \
    base local. Used to materialise the owned part of the PCG beyond the existing init-tree shape so \
    that each target place becomes reachable via an unbroken chain of unpack edges. Because sibling \
    places at each synthetic step are unknown without type information, the expansion of every \
    emitted edge contains just the single child that extends the prefix.")
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
  projUnpackChain ‹p↦«local», [], p↦projection›

defFn localsUnpackEdges (.plain "localsUnpackEdges")
  (doc! "For every allocated local in an owned state, collect the unpack edges derived from that \
    local's initialisation tree. Unallocated slots contribute nothing. The local index carried by \
    each entry is recovered from the list position via `zipIdx`.")
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

defFn init (.plain "init")
  (doc! "The initial PCG data at the entry of a MIR body: \
    an empty borrows graph, the per-local owned state \
    computed via #OwnedState.initial, basic block 0 as the \
    starting program point, and no transient state.")
  (body "The function body." : Body)
  : PcgData Place :=
    PcgData⟨BorrowsGraph⟨mapEmpty‹›⟩,
      OwnedState.initial ‹body›,
      BasicBlockIdx⟨0⟩, None⟩

defFn join (.plain "join")
  (doc! "Join two PCG data values at the program-point entry of basic block `bb`: pointwise-join \
    the borrows graphs and meet the owned states (per-local, via `OwnedState.meet`), tag the result \
    with `bb` as its current basic block, and reset `transientState` to `None` — the transient \
    read/write-borrow side condition is local to a single program point and does not propagate \
    across joins.")
  (pd1 "The first PCG data." : PcgData Place)
  (pd2 "The second PCG data." : PcgData Place)
  (bb "The basic block of the joined program point."
      : BasicBlockIdx)
  requires pd1↦os↦locals·length
             = pd2↦os↦locals·length
  : PcgData Place :=
    PcgData⟨
      BorrowsGraph.join ‹pd1↦bg, pd2↦bg›,
      OwnedState.meet
        ‹pd1↦os, pd2↦os,
         proof[h_pre0]›,
      bb,
      None⟩

end PcgData

defFn transientReadPlaces (.plain "transientReadPlaces")
  (doc! "Extract the read-place set from the optional transient place: returns the carried set when \
    `transientState` is #TransientState.readPlaces, and the empty list otherwise (`None` or a \
    write-borrowed place).")
  (tp "The optional transient place."
      : Option (TransientState Place))
  : List Place where
  | .some (.readPlaces s) => s·toList
  | _ => []

defFn edges (.plain "edges")
  (doc! "All PCG hyperedges represented by the per-program-point PCG data. The result is the union \
    of three sources: (1) unpack edges derived from the internal structure of each allocated owned \
    init tree, (2) unpack edges materialising the tree further to reach every place in the transient \
    read-place set (when `transientState` carries #TransientState.readPlaces) and every owned place \
    blocked by a deref edge, and (3) every edge already recorded in the borrows graph.")
  (pd "The PCG data." : PcgData Place)
  : List (PcgEdge Place) :=
    let treeEdges := localsUnpackEdges ‹pd↦os↦locals› ;
    let targets := transientReadPlaces ‹pd↦transientState›
      ++ BorrowsGraph.blockedCurrentPlaces ‹pd↦bg› ;
    let matEdges := targets·flatMap fun p => placeUnpackChain ‹p› ;
    let unpackEdges := (treeEdges ++ matEdges)
      ·map fun ue => PcgEdge.unpack ‹ue› ;
    unpackEdges ++ pd↦bg↦edges·toList·map fun ⟨e, _⟩ => e
