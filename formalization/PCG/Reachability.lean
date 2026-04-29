import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import PCG.PcgData

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
-- Endpoint → PcgNode lifters
-- ══════════════════════════════════════════════

defFn mlpNode (.plain "mlpNode")
  (.plain "Lift a maybe-labelled place to a PCG node by \
    wrapping it in a `PcgPlace.maybeLabelled` and then a \
    `PcgNode.place`.")
  (mlp "The maybe-labelled place." : MaybeLabelled Place)
  : PcgNode Place :=
    PcgNode.place ‹PcgPlace.maybeLabelled ‹mlp››

defFn pcgLpNode (.plain "pcgLpNode")
  (.plain "Lift a PCG lifetime projection to a PCG node by \
    wrapping it in `PcgNode.lifetimeProjection`.")
  (lp "The PCG lifetime projection."
      : PcgLifetimeProjection Place)
  : PcgNode Place :=
    PcgNode.lifetimeProjection ‹lp›

-- ══════════════════════════════════════════════
-- Per-edge out-neighbours
-- ══════════════════════════════════════════════

defFn edgeTargets (.plain "edgeTargets")
  (.seq [.plain "The list of nodes that ", .code "a",
    .plain " directly reaches via a single PCG edge ",
    .code "e", .plain ". An unpack edge contributes its \
    expansion when ", .code "a", .plain " is the base; a \
    deref edge contributes the deref place when ",
    .code "a", .plain " is the blocked place; a borrow \
    edge contributes the assigned reference when ",
    .code "a", .plain " is the blocked place. Borrow-flow \
    and abstraction edges have target endpoints in \
    lifetime-projection types with no direct ",
    .code "PcgNode", .plain " lifter and contribute no \
    targets here, making the search a sound under-\
    approximation."])
  (e "The PCG edge." : PcgEdge Place)
  (a "The candidate source node." : PcgNode Place)
  : List (PcgNode Place) where
  | .unpack ue ; a =>
      if a == ue↦base then ue↦expansion else []
  | .deref de ; a =>
      if a == mlpNode ‹de↦blockedPlace› then
        [mlpNode ‹de↦derefPlace›]
      else []
  | .borrow be ; a =>
      if a == mlpNode ‹be↦blocked› then
        [mlpNode ‹be↦assignedRef›]
      else []
  | .borrowFlow _ ; _ => []
  | .abstraction _ ; _ => []

defFn nodeNeighbors (.plain "nodeNeighbors")
  (.seq [.plain "All nodes that ", .code "a",
    .plain " directly reaches in ", .code "pd",
    .plain ": the concatenation of ", .code "edgeTargets",
    .plain " over every edge in ", .code "edges",
    .plain "."])
  (pd "The PCG data." : PcgData Place)
  (a "The candidate source node." : PcgNode Place)
  : List (PcgNode Place) :=
    edges ‹pd›·flatMap fun e => edgeTargets ‹e, a›

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
  | .deref de => [mlpNode ‹de↦derefPlace›]
  | .borrow be => [mlpNode ‹be↦assignedRef›]
  | .borrowFlow _ => []
  | .abstraction _ => []

defFn candidateNodes (.plain "candidateNodes")
  (.seq [.plain "An upper bound on the set of nodes the \
    reachability search starting from ", .code "start",
    .plain " could ever visit: the start node together with \
    every target node appearing in some edge of ",
    .code "pd", .plain ". Initialises the ",
    .code "unvisited", .plain " parameter of ",
    .code "reachableSearch", .plain " — every node the \
    search actually expands belongs to this list, so erasing \
    one per expansion strictly shrinks its length."])
  (pd "The PCG data." : PcgData Place)
  (start "The starting node." : PcgNode Place)
  : List (PcgNode Place) :=
    start :: edges ‹pd›·flatMap fun e =>
      edgeAllTargets ‹e›

-- ══════════════════════════════════════════════
-- Graph search with cycle detection
-- ══════════════════════════════════════════════

/-- Walk the PCG with cycle detection: pop the head of
    `frontier`, return `true` on a target hit, skip when the
    head is no longer in `unvisited` (already expanded), and
    otherwise expand by erasing the head from `unvisited` and
    prepending its neighbours to the frontier.

    Termination is the lexicographic measure
    `(unvisited.length, frontier.length)`: every skip
    iteration shrinks `frontier`, every expand iteration
    shrinks `unvisited` (because the `if h : ... then` branch
    establishes that the head is in `unvisited`, so
    `List.erase` removes it). Lean's structural-recursion
    check is not enough here, but the lex measure is, and we
    discharge the obligations with `Prod.Lex.right` /
    `Prod.Lex.left` and `List.length_erase_of_mem` /
    `List.any_eq_true`. -/
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
    | (-- Expand recursive call: `h : (unvisited.any
       -- (· == x)) = true`. After `Prod.Lex.left` the goal
       -- is `(unvisited.filter (· != x)).length <
       -- unvisited.length`. Rewrite via
       -- `length_filter_lt_length_iff_exists` and discharge
       -- with the witness `y` produced by `h`.
       apply Prod.Lex.left
       rw [List.length_filter_lt_length_iff_exists]
       have ⟨y, hy_mem, hy_eq⟩ :=
         List.any_eq_true.mp h
       refine ⟨y, hy_mem, ?_⟩
       simp [bne, hy_eq])
    | (-- Skip recursive call: `Prod.Lex.right` reduces to a
       -- frontier-component inequality discharged by `omega`.
       apply Prod.Lex.right; omega)

-- ══════════════════════════════════════════════
-- User-facing properties
-- ══════════════════════════════════════════════

defProperty reachableFrom (.plain "reachableFrom")
  short (pdDoc, aDoc, bDoc) =>
    (.seq [bDoc, .plain " is reachable from ", aDoc,
           .plain " in ", pdDoc])
  long (pdDoc, aDoc, bDoc) =>
    (.seq [bDoc, .plain " is reachable from ", aDoc,
           .plain " in ", pdDoc, .plain ": ",
           .code "reachableSearch",
           .plain " starting from ", aDoc,
           .plain " finds ", bDoc, .plain " by walking the \
           PCG with cycle detection."])
  (pd "The PCG data." : PcgData Place)
  (a "The starting node." : PcgNode Place)
  (b "The candidate target node." : PcgNode Place)
  := reachableSearch
       ‹pd, b, [a], candidateNodes ‹pd, a››

defProperty connected (.plain "connected")
  short (pdDoc, aDoc, bDoc) =>
    (.seq [aDoc, .plain " and ", bDoc,
           .plain " are connected in ", pdDoc])
  long (pdDoc, aDoc, bDoc) =>
    (.seq [aDoc, .plain " and ", bDoc,
           .plain " are connected in ", pdDoc,
           .plain ": one of the two nodes is reachable \
           from the other along the directed edge \
           relation."])
  (pd "The PCG data." : PcgData Place)
  (a "The first node." : PcgNode Place)
  (b "The second node." : PcgNode Place)
  := reachableFrom ‹pd, a, b› ∨ reachableFrom ‹pd, b, a›
