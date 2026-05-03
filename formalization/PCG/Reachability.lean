import Core.Doc.Interp
import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw
import PCG.PcgData
import PCG.PlaceCapability

/-! # PCG reachability

Defines node-level reachability over the PCG hypergraph: when
can node `b` be reached from node `a` by following a sequence
of edges in `pd`, and when are two nodes connected (i.e. one
of the two is reachable from the other).

Reachability is computed by an explicit graph walk
(`reachableSearch`) that maintains an `unvisited` list of
nodes still eligible for expansion. Each recursive call either
pops an already-expanded node (frontier shrinks) or expands a
fresh node, removing it from `unvisited` (unvisited shrinks).
The lexicographic measure `(unvisited.length, frontier.length)`
strictly decreases on every recursive call — a real
well-founded termination argument, no fuel parameter required.

The PCG is a directed hypergraph with five edge kinds (see
`PcgEdge`); each edge has a natural source / target reading,
captured by `edgeTargets` below. Some edge kinds (`borrowFlow`,
`abstraction`) carry endpoints in lifetime-projection types
that have no clean lift to `PcgNode P`. To avoid an explosion
of conversion helpers, those endpoints are skipped: only the
cleanly-liftable ones (`MaybeLabelled Place` →
`PcgNode.place`, `PcgLifetimeProjection Place` →
`PcgNode.lifetimeProjection`) contribute step targets. As a
result `reachableFrom` is a sound lower bound on the true
hypergraph reachability — not necessarily complete for paths
that thread through unmodelled lifetime-projection nodes. -/

-- ══════════════════════════════════════════════
-- Per-edge out-neighbours
-- ══════════════════════════════════════════════

defFn edgeTargets (.plain "edgeTargets")
  (doc! "The list of nodes that `a` directly reaches via a single PCG edge `e`. An unpack edge \
    contributes its expansion when `a` is the base; a deref edge contributes the deref place when \
    `a` is the blocked place; a borrow edge contributes the assigned reference when `a` is the \
    blocked place. Borrow-flow and abstraction edges have target endpoints in lifetime-projection \
    types with no direct #PcgNode lifter and contribute no targets here, making the search a sound \
    under-approximation.")
  (e "The PCG edge." : PcgEdge Place)
  (a "The candidate source node." : PcgNode Place)
  : List (PcgNode Place) where
  | .unpack ue ; a =>
      if a == ue↦base then ue↦expansion else []
  | .deref de ; a =>
      if a == mlpNode de↦blockedPlace then
        [mlpNode de↦derefPlace]
      else []
  | .borrow be ; a =>
      if a == mlpNode be↦blocked then
        [mlpNode be↦assignedRef]
      else []
  | .borrowFlow _ ; _ => []
  | .abstraction _ ; _ => []

defFn nodeNeighbors (.plain "nodeNeighbors")
  (doc! "All nodes that {a} directly reaches in {pd}: \
         the concatenation of #edgeTargets over every \
         edge in #edges.")
  (pd "The PCG data." : PcgData Place)
  (a "The candidate source node." : PcgNode Place)
  : List (PcgNode Place) :=
    edges pd·flatMap fun e => edgeTargets e a

-- ══════════════════════════════════════════════
-- Candidate node universe
-- ══════════════════════════════════════════════

defFn edgeAllTargets (.plain "edgeAllTargets")
  (.plain "Every target node of a PCG edge, irrespective of \
    its source. Used to bound the set of nodes the \
    reachability search could ever visit.")
  (e "The PCG edge." : PcgEdge Place)
  : List (PcgNode Place) where
  | .unpack ue => ue↦expansion
  | .deref de => [mlpNode de↦derefPlace]
  | .borrow be => [mlpNode be↦assignedRef]
  | .borrowFlow _ => []
  | .abstraction _ => []

defFn candidateNodes (.plain "candidateNodes")
  (doc! "An upper bound on the set of nodes the reachability search starting from `start` could \
    ever visit: the start node together with every target node appearing in some edge of `pd`. \
    Initialises the `unvisited` parameter of `reachableSearch` — every node the search actually \
    expands belongs to this list, so erasing one per expansion strictly shrinks its length.")
  (pd "The PCG data." : PcgData Place)
  (start "The starting node." : PcgNode Place)
  : List (PcgNode Place) :=
    start :: edges pd·flatMap fun e =>
      edgeAllTargets e

open BorrowsGraph in
defFn places (.plain "places")
  (doc! "The set of MIR places tracked by the PCG {pd}: \
    every place reached by walking an allocated owned \
    local's initialisation tree (via #itPlaces), together \
    with every place appearing as an endpoint of a deref or \
    borrow edge in {pd}. Borrow-flow and abstraction edges \
    have lifetime-projection endpoints that don't lift into \
    a place; unpack-edge endpoints sit at the general \
    `PcgNode Place` level and are reached implicitly via \
    the owned-state walk, so neither contributes here. Used \
    as the `p ∈ places pcg` antecedent of \
    #[ConnectedInvariant] to constrain the property to places \
    the PCG actually tracks: places with no corresponding \
    entry carry no analysis guarantee, and the invariant \
    holds for them vacuously.")
  (pd "The PCG data." : PcgData Place)
  : Set Place :=
    let owned := pd↦os↦locals·zipIdx·setFlatMap fun ⟨ol, idx⟩ =>
      match ol with
      | .allocated t => itPlaces t Local⟨idx⟩ []
      | .unallocated => ∅
      end ;
    let edgeP := (edges pd)·setFlatMap fun e =>
      match e with
      | .deref de =>
          (currentPlace de↦blockedPlace)·toSet ∪
            (currentPlace de↦derefPlace)·toSet
      | .borrow be =>
          (currentPlace be↦blocked)·toSet ∪
            (currentPlace be↦assignedRef)·toSet
      | _ => ∅
      end ;
    owned ∪ edgeP

-- ══════════════════════════════════════════════
-- Graph search with cycle detection
-- ══════════════════════════════════════════════

-- The graph walk uses `termination_by` and a custom
-- `decreasing_by` proof, neither of which the DSL surface
-- can express today. `defRaw` exposes the inner declaration
-- to Lean directly (so the IDE keeps highlighting / hover /
-- gotoDef on it) and registers its verbatim source for the
-- export pipeline.
defRaw beforeProperties =>
/-- Walk the PCG with cycle detection. The lexicographic
    measure `(unvisited.length, frontier.length)` strictly
    decreases on every recursive call: the skip iteration
    shrinks `frontier`, the expand iteration shrinks
    `unvisited` (the `if h : unvisited.any (· == x)`
    hypothesis guarantees the head is in `unvisited`, so
    `List.filter (· != x)` removes it). The `defProperty`
    `reachableFrom` below wraps this with the appropriate
    initial state. -/
def reachableSearch
    (pd : PcgData Place)
    (target : PcgNode Place)
    (frontier : List (PcgNode Place))
    (unvisited : List (PcgNode Place))
    : Bool :=
  match frontier with
  | [] => false
  | x :: rest =>
      if x == target then true
      else if h : unvisited.any (· == x) then
        reachableSearch pd target
          (nodeNeighbors pd x ++ rest)
          (unvisited.filter fun y => y != x)
      else
        reachableSearch pd target rest unvisited
termination_by (unvisited.length, frontier.length)
decreasing_by
  all_goals
    simp_wf
    first
    | (apply Prod.Lex.left
       rw [List.length_filter_lt_length_iff_exists]
       have ⟨y, hy_mem, hy_eq⟩ :=
         List.any_eq_true.mp h
       refine ⟨y, hy_mem, ?_⟩
       simp [bne, hy_eq])
    | (apply Prod.Lex.right; omega)

-- ══════════════════════════════════════════════
-- User-facing properties
-- ══════════════════════════════════════════════

defProperty reachableFrom (.plain "reachableFrom")
  short
    (doc! "{b} is reachable from {a} in {pd}")
  long
    (doc! "{b} is reachable from {a} in {pd}: \
      `reachableSearch` starting from {a} finds {b} by \
      walking the PCG with cycle detection.")
  (pd "The PCG data." : PcgData Place)
  (a "The starting node." : PcgNode Place)
  (b "The candidate target node." : PcgNode Place)
  := reachableSearch
       pd b [a] (candidateNodes pd a)

defProperty connected (.plain "connected")
  short
    (doc! "{a} and {b} are connected in {pd}")
  long
    (doc! "{a} and {b} are connected in {pd}: one of the two \
      nodes is reachable from the other along the directed \
      edge relation.")
  (pd "The PCG data." : PcgData Place)
  (a "The first node." : PcgNode Place)
  (b "The second node." : PcgNode Place)
  := reachableFrom pd a b ∨ reachableFrom pd b a
