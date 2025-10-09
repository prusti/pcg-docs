/**
 * Coupling algorithms for hypergraphs
 *
 * These algorithms compute which edges should be coupled together based on
 * different definitions of when edges must expire simultaneously.
 */

interface Node {
    id: string;
    x?: number;
    y?: number;
    place?: string;
    lifetime?: string;
    label?: string;
}

interface Edge {
    id?: string;
    sources?: string[];
    targets?: string[];
    label?: string;
    originalIndex?: number;
}

interface CoupledEdgeResult {
    type: string;
    underlyingEdges: InternalEdge[];
    frontier?: string[];
    sources: string[];
    targets: string[];
}

/**
 * Represents a coupled edge constructed from a set of underlying edges
 */
class CoupledEdge {
    underlyingEdges: InternalEdge[];
    sources: string[];
    targets: string[];

    constructor(underlyingEdges: InternalEdge[]) {
        this.underlyingEdges = underlyingEdges;

        const allSources = new Set<string>();
        const allTargets = new Set<string>();

        underlyingEdges.forEach(edge => {
            edge.sources.forEach(s => allSources.add(s));
            edge.targets.forEach(t => allTargets.add(t));
        });

        this.sources = Array.from(allSources).filter(s => !allTargets.has(s));
        this.targets = Array.from(allTargets).filter(t => !allSources.has(t));
    }
}

interface InternalEdge {
    id: string;
    sources: string[];
    targets: string[];
    originalIndex?: number;
}

/**
 * Graph representation for coupling algorithms
 */
class HypergraphForCoupling {
    nodes: Set<string>;
    edges: InternalEdge[];

    constructor(nodes: Node[], edges: Edge[]) {
        this.nodes = new Set(nodes.map(n => n.id));
        this.edges = edges
            .filter(e => e.sources && e.targets)
            .map((e, idx) => ({
                id: e.id || `edge-${idx}`,
                sources: e.sources || [],
                targets: e.targets || [],
                originalIndex: idx
            }));
    }

    /**
     * Clone this graph
     */
    clone(): HypergraphForCoupling {
        return new HypergraphForCoupling(
            Array.from(this.nodes).map(id => ({ id })),
            this.edges.map(e => ({...e}))
        );
    }

    /**
     * Remove a set of nodes and all edges containing them
     */
    removeNodes(nodeSet: string[]): void {
        const nodesToRemove = new Set(nodeSet);
        this.nodes = new Set(Array.from(this.nodes).filter(n => !nodesToRemove.has(n)));
        this.edges = this.edges.filter(e => {
            const hasRemovedSource = e.sources.some(s => nodesToRemove.has(s));
            const hasRemovedTarget = e.targets.some(t => nodesToRemove.has(t));
            return !hasRemovedSource && !hasRemovedTarget;
        });
    }

    /**
     * Get all nodes that are blocked (not leaves) in this graph
     */
    getBlockedNodes(): string[] {
        const leaves = this.getLeafNodes();
        return Array.from(this.nodes).filter(n => !leaves.has(n));
    }

    /**
     * Get all leaf nodes (nodes with no outgoing edges)
     */
    getLeafNodes(): Set<string> {
        const sourcesInEdges = new Set<string>();
        this.edges.forEach(e => {
            e.sources.forEach(s => sourcesInEdges.add(s));
        });

        return new Set(Array.from(this.nodes).filter(n => !sourcesInEdges.has(n)));
    }

    /**
     * Get all descendants of a node (reflexive, transitive closure)
     */
    getDescendants(nodeId: string): Set<string> {
        const descendants = new Set<string>([nodeId]);
        const toVisit = [nodeId];

        while (toVisit.length > 0) {
            const current = toVisit.pop()!;

            this.edges.forEach(e => {
                if (e.sources.includes(current)) {
                    e.targets.forEach(t => {
                        if (!descendants.has(t)) {
                            descendants.add(t);
                            toVisit.push(t);
                        }
                    });
                }
            });
        }

        return descendants;
    }

    /**
     * Check if a set of nodes forms a frontier (closed under descendants)
     */
    isFrontier(nodeSet: string[]): boolean {
        const frontier = new Set(nodeSet);

        for (const node of nodeSet) {
            const descendants = this.getDescendants(node);
            for (const desc of descendants) {
                if (!frontier.has(desc)) {
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * Get all nodes that would be unblocked by removing the given frontier
     */
    getUnblockedNodes(frontier: string[]): string[] {
        const frontierSet = new Set(frontier);
        const graph = this.clone();
        graph.removeNodes(frontier);

        const originalBlocked = this.getBlockedNodes();
        const newLeaves = graph.getLeafNodes();

        return originalBlocked.filter(n =>
            !frontierSet.has(n) && newLeaves.has(n)
        );
    }

    /**
     * Check if removing a frontier makes at least one node accessible (productive)
     */
    isProductiveExpiry(frontier: string[]): boolean {
        return this.getUnblockedNodes(frontier).length > 0;
    }

    /**
     * Get all possible frontiers of the graph
     */
    getAllFrontiers(): string[][] {
        const nodes = Array.from(this.nodes);
        const frontiers: string[][] = [];

        const numSubsets = Math.pow(2, nodes.length);
        for (let i = 1; i < numSubsets; i++) {
            const subset: string[] = [];
            for (let j = 0; j < nodes.length; j++) {
                if (i & (1 << j)) {
                    subset.push(nodes[j]);
                }
            }

            if (this.isFrontier(subset)) {
                frontiers.push(subset);
            }
        }

        return frontiers;
    }

    /**
     * Get minimal productive frontiers
     */
    getMinimalProductiveFrontiers(): string[][] {
        const allFrontiers = this.getAllFrontiers();
        const productiveFrontiers = allFrontiers.filter(f => this.isProductiveExpiry(f));

        return productiveFrontiers.filter(f1 => {
            return !productiveFrontiers.some(f2 => {
                if (f1 === f2) return false;

                const f1Set = new Set(f1);
                const f2Set = new Set(f2);

                if (f2.length >= f1.length) return false;

                return f2.every(node => f1Set.has(node));
            });
        });
    }

    /**
     * Get edges that are removed when a frontier expires
     */
    getExpiryEdges(frontier: string[]): InternalEdge[] {
        const frontierSet = new Set(frontier);
        return this.edges.filter(e => {
            const hasRemovedSource = e.sources.some(s => frontierSet.has(s));
            const hasRemovedTarget = e.targets.some(t => frontierSet.has(t));
            return hasRemovedSource || hasRemovedTarget;
        });
    }

    isEmpty(): boolean {
        return this.edges.length === 0;
    }
}

/**
 * Represents an unblocking of a graph - an ordered partition of non-root nodes
 */
interface Unblocking {
    partitions: string[][];
    reachableGraphs: HypergraphForCoupling[];
}

/**
 * Coupling algorithm based on frontier expiries
 *
 * This algorithm generates coupled edges by finding maximally coupled edges.
 * Edges are effectively coupled if for all reachable subgraphs in distinct
 * unblockings, the graph contains either all edges or none of them.
 *
 * From coupling.md lines 243-269:
 * An unblocking U is an ordered partitioning of non-root nodes satisfying
 * that there exists a frontier with an expiry that unblocks all nodes in the
 * first partition, and the remaining partitions form an unblocking of the
 * reduced graph.
 *
 * Edges are effectively coupled if they appear together in all reachable
 * subgraphs. Maximally coupled edges are effectively coupled sets that are
 * not subsets of other effectively coupled sets.
 */
function computeCouplingFrontierExpiries(nodes: Node[], edges: Edge[]): CoupledEdgeResult[] {
    const graph = new HypergraphForCoupling(nodes, edges);

    const allUnblockings = computeAllUnblockings(graph);
    const distinctUnblockings = getDistinctUnblockings(allUnblockings);

    const reachableGraphs = new Set<HypergraphForCoupling>();
    for (const unblocking of distinctUnblockings) {
        for (const g of unblocking.reachableGraphs) {
            reachableGraphs.add(g);
        }
    }

    const edgeIds = graph.edges.map(e => e.id);
    const effectivelyCoupled = findEffectivelyCoupledSets(
        Array.from(reachableGraphs),
        edgeIds
    );

    const maximallyCoupled = findMaximallyCoupledSets(effectivelyCoupled);

    return maximallyCoupled.map((edgeIdSet, idx) => {
        const underlyingEdges = graph.edges.filter(e => edgeIdSet.has(e.id));
        const coupled = new CoupledEdge(underlyingEdges);
        return {
            type: 'coupled',
            underlyingEdges: underlyingEdges,
            sources: coupled.sources,
            targets: coupled.targets
        };
    });
}

/**
 * Compute all unblockings of a graph
 */
function computeAllUnblockings(graph: HypergraphForCoupling): Unblocking[] {
    if (graph.isEmpty()) {
        return [];
    }

    const blockedNodes = graph.getBlockedNodes();
    if (blockedNodes.length === 0) {
        return [];
    }

    const result: Unblocking[] = [];
    const frontiers = graph.getAllFrontiers();
    const productiveFrontiers = frontiers.filter(f => graph.isProductiveExpiry(f));

    for (const frontier of productiveFrontiers) {
        const unblockedNodes = graph.getUnblockedNodes(frontier);
        if (unblockedNodes.length === 0) continue;

        const remainingGraph = graph.clone();
        remainingGraph.removeNodes(frontier);

        const recursiveUnblockings = computeAllUnblockings(remainingGraph);

        if (recursiveUnblockings.length === 0) {
            result.push({
                partitions: [unblockedNodes],
                reachableGraphs: [graph, remainingGraph]
            });
        } else {
            for (const subUnblocking of recursiveUnblockings) {
                result.push({
                    partitions: [unblockedNodes, ...subUnblocking.partitions],
                    reachableGraphs: [graph, ...subUnblocking.reachableGraphs]
                });
            }
        }
    }

    return result;
}

/**
 * Get distinct unblockings (remove non-minimal w.r.t subsumption)
 */
function getDistinctUnblockings(unblockings: Unblocking[]): Unblocking[] {
    return unblockings.filter(u1 => {
        return !unblockings.some(u2 => {
            if (u1 === u2) return false;
            return isImmediatelySubsumedBy(u1, u2);
        });
    });
}

/**
 * Check if u1 is immediately subsumed by u2
 */
function isImmediatelySubsumedBy(u1: Unblocking, u2: Unblocking): boolean {
    if (u1.partitions.length !== u2.partitions.length - 1) {
        return false;
    }

    for (let i = 0; i <= u1.partitions.length; i++) {
        const merged = new Set([
            ...u1.partitions[i] || [],
            ...u1.partitions[i + 1] || []
        ]);

        const u2Part = new Set(u2.partitions[i] || []);

        if (merged.size === u2Part.size &&
            Array.from(merged).every(n => u2Part.has(n))) {

            let beforeMatch = true;
            for (let j = 0; j < i; j++) {
                const u1Set = new Set(u1.partitions[j]);
                const u2Set = new Set(u2.partitions[j]);
                if (u1Set.size !== u2Set.size ||
                    !Array.from(u1Set).every(n => u2Set.has(n))) {
                    beforeMatch = false;
                    break;
                }
            }

            if (!beforeMatch) continue;

            let afterMatch = true;
            for (let j = i + 1; j < u1.partitions.length; j++) {
                const u1Set = new Set(u1.partitions[j]);
                const u2Set = new Set(u2.partitions[j + 1] || []);
                if (u1Set.size !== u2Set.size ||
                    !Array.from(u1Set).every(n => u2Set.has(n))) {
                    afterMatch = false;
                    break;
                }
            }

            if (afterMatch) return true;
        }
    }

    return false;
}

/**
 * Find all effectively coupled sets of edges
 */
function findEffectivelyCoupledSets(
    reachableGraphs: HypergraphForCoupling[],
    edgeIds: string[]
): Set<string>[] {
    const effectivelyCoupled: Set<string>[] = [];

    const numSubsets = Math.pow(2, edgeIds.length);
    for (let i = 1; i < numSubsets; i++) {
        const subset: string[] = [];
        for (let j = 0; j < edgeIds.length; j++) {
            if (i & (1 << j)) {
                subset.push(edgeIds[j]);
            }
        }

        if (isEffectivelyCoupled(subset, reachableGraphs)) {
            effectivelyCoupled.push(new Set(subset));
        }
    }

    return effectivelyCoupled;
}

/**
 * Check if a set of edges is effectively coupled
 */
function isEffectivelyCoupled(
    edgeIds: string[],
    reachableGraphs: HypergraphForCoupling[]
): boolean {
    const edgeSet = new Set(edgeIds);

    for (const graph of reachableGraphs) {
        const graphEdgeIds = new Set(graph.edges.map(e => e.id));

        const containsAll = edgeIds.every(id => graphEdgeIds.has(id));
        const containsNone = edgeIds.every(id => !graphEdgeIds.has(id));

        if (!containsAll && !containsNone) {
            return false;
        }
    }

    return true;
}

/**
 * Find maximally coupled sets (not subsets of other effectively coupled sets)
 */
function findMaximallyCoupledSets(effectivelyCoupled: Set<string>[]): Set<string>[] {
    return effectivelyCoupled.filter(set1 => {
        return !effectivelyCoupled.some(set2 => {
            if (set1 === set2) return false;

            if (set1.size >= set2.size) return false;

            return Array.from(set1).every(id => set2.has(id));
        });
    });
}

/**
 * Identity coupling - returns each edge as its own coupled edge
 * This is useful as a baseline comparison
 */
function computeCouplingIdentity(nodes: Node[], edges: Edge[]): CoupledEdgeResult[] {
    return edges.map((e, idx) => ({
        type: 'identity',
        underlyingEdges: [{
            id: e.id || `edge-${idx}`,
            sources: e.sources || [],
            targets: e.targets || [],
            originalIndex: idx
        }],
        sources: e.sources || [],
        targets: e.targets || []
    }));
}

interface CouplingAlgorithm {
    name: string;
    description: string;
    compute: (nodes: Node[], edges: Edge[]) => CoupledEdgeResult[];
}

/**
 * Available coupling algorithms
 */
export const COUPLING_ALGORITHMS: Record<string, CouplingAlgorithm> = {
    'none': {
        name: 'None (Original)',
        description: 'Show original edges without coupling',
        compute: computeCouplingIdentity
    },
    'frontier-expiries': {
        name: 'Frontier Expiries',
        description: 'Maximal coupling based on frontier expiries',
        compute: computeCouplingFrontierExpiries
    }
};

/**
 * Apply coupling algorithm to a graph
 */
export function applyCouplingAlgorithm(algorithmId: string, nodes: Node[], edges: Edge[]): CoupledEdgeResult[] {
    const algorithm = COUPLING_ALGORITHMS[algorithmId];
    if (!algorithm) {
        throw new Error(`Unknown coupling algorithm: ${algorithmId}`);
    }

    return algorithm.compute(nodes, edges);
}

export {
    HypergraphForCoupling,
    computeAllUnblockings,
    getDistinctUnblockings,
    findEffectivelyCoupledSets,
    findMaximallyCoupledSets,
    isEffectivelyCoupled
};

