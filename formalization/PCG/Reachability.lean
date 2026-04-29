import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefInductiveProperty
import PCG.PcgData

/-! # PCG reachability

Defines node-level reachability over the PCG hypergraph: when
can node `b` be reached from node `a` by following a sequence
of edges in `pd`, and when are two nodes connected (i.e. one
of the two is reachable from the other).

The PCG is a directed hypergraph with five edge kinds (see
`PcgEdge`); each edge has a natural source / target reading,
captured by `edgeStep` below. `directlyConnected` lifts that
to a per-`PcgData` step relation, `ReachableInPcg` takes the
reflexive-transitive closure as a `defInductiveProperty`, and
the user-facing `reachableFrom` / `connected` properties wrap
the inductive.

Some edge kinds (function-call abstraction edges; the
`borrowFlow` edge's local-lifetime-projection target;
abstraction loop edges' lifetime-projection source) carry
endpoints that live in lifetime-projection types rather than
`PcgNode P` directly. To avoid an explosion of conversion
helpers, the step relation handles those endpoints
conservatively: it lifts what wraps cleanly (each
`MaybeLabelled Place` becomes a `PcgNode.place`; each
`PcgLifetimeProjection Place` becomes a
`PcgNode.lifetimeProjection`) and ignores the rest. As a
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
-- Direct edge step
-- ══════════════════════════════════════════════

defFn edgeStep (.plain "edgeStep")
  (.seq [.plain "Whether a single PCG edge ", .code "e",
    .plain " has a directed step from ", .code "a",
    .plain " to ", .code "b", .plain ". The step relation \
    is defined per edge kind: an unpack edge steps from its \
    base to each child of its expansion; a deref edge steps \
    from the blocked place to the deref place; a borrow edge \
    steps from the blocked place to the assigned reference; \
    a borrow-flow edge steps from its source projection \
    (lifted via ", .code "pcgLpNode", .plain ") — the \
    local-lifetime-projection target is omitted because no \
    direct ", .code "PcgNode",
    .plain " lifter is provided for it. Abstraction edges \
    are not modelled."])
  (e "The PCG edge." : PcgEdge Place)
  (a "The candidate source node." : PcgNode Place)
  (b "The candidate target node." : PcgNode Place)
  : Bool where
  | .unpack ue ; a ; b =>
      a == ue↦base ∧
        ue↦expansion·any fun n => b == n
  | .deref de ; a ; b =>
      a == mlpNode ‹de↦blockedPlace› ∧
        b == mlpNode ‹de↦derefPlace›
  | .borrow be ; a ; b =>
      a == mlpNode ‹be↦blocked› ∧
        b == mlpNode ‹be↦assignedRef›
  | .borrowFlow bfe ; a ; _ =>
      -- Source side only: the local-lifetime-projection
      -- target has no direct `PcgNode` lifter, so this
      -- edge contributes no step targets. Falls through to
      -- the `False` arm.
      a == pcgLpNode ‹bfe↦source› ∧ false
  | .abstraction _ ; _ ; _ => false

-- ══════════════════════════════════════════════
-- One-step / transitive reachability
-- ══════════════════════════════════════════════

defFn directlyConnected (.plain "directlyConnected")
  (.seq [.plain "Whether some edge in ", .code "pd",
    .plain "'s edge set has a directed step from ",
    .code "a", .plain " to ", .code "b",
    .plain " under ", .code "edgeStep", .plain "."])
  (pd "The PCG data." : PcgData Place)
  (a "The candidate source node." : PcgNode Place)
  (b "The candidate target node." : PcgNode Place)
  : Bool :=
    edges ‹pd›·any fun e =>
      edgeStep ‹e, a, b›

defInductiveProperty ReachableInPcg
  "ReachableInPcg PCG Nodes"
  (.seq [.plain "Reflexive-transitive closure of the \
    one-step ", .code "directlyConnected",
    .plain " relation over the PCG. ",
    .code "ReachableInPcg pd a b", .plain " holds when ",
    .code "b", .plain " can be reached from ", .code "a",
    .plain " by following zero or more edges of ",
    .code "pd", .plain "."])
  (pd "The PCG data." : PcgData Place)
  (a "The starting node." : PcgNode Place)
  (b "The reachable node." : PcgNode Place)
where
  | refl {pd : PcgData Place} {a : PcgNode Place}
      ⊢ ReachableInPcg ‹pd, a, a›
  | step {pd : PcgData Place}
        {a, b, c : PcgNode Place}
      from (directlyConnected ‹pd, a, b› = true,
            ReachableInPcg ‹pd, b, c›)
      ⊢ ReachableInPcg ‹pd, a, c›

-- ══════════════════════════════════════════════
-- User-facing properties
-- ══════════════════════════════════════════════

defProperty reachableFrom (.plain "reachableFrom")
  short (pdDoc, aDoc, bDoc) =>
    (.seq [bDoc, .plain " is reachable from ", aDoc,
           .plain " in ", pdDoc])
  long (pdDoc, aDoc, bDoc) =>
    (.seq [bDoc, .plain " is reachable from ", aDoc,
           .plain " in ", pdDoc, .plain ": there is a \
           sequence of zero or more PCG edges in ", pdDoc,
           .plain " whose ", .code "edgeStep",
           .plain " connects ", aDoc, .plain " to ", bDoc,
           .plain "."])
  (pd "The PCG data." : PcgData Place)
  (a "The starting node." : PcgNode Place)
  (b "The candidate target node." : PcgNode Place)
  := ReachableInPcg ‹pd, a, b›

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
