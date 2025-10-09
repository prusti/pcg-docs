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
 * Coupling algorithm based on productive expiries
 *
 * This algorithm generates coupled edges by finding minimal productive expiries.
 * A productive expiry is one that makes at least one blocked node accessible.
 *
 * From coupling.md lines 270-293:
 * 1. Let C = ∅ be the set of coupled edges
 * 2. While G contains any hyperedges:
 *    a. For each frontier S that defines a minimal productive expiry of G:
 *       i. Add the expiry edge of S to C
 *       ii. C ← C ∪ couple(G \ S)
 * 3. Return C
 */
function computeCouplingProductiveExpiries(nodes: Node[], edges: Edge[]): CoupledEdgeResult[] {
    const graph = new HypergraphForCoupling(nodes, edges);

    function couple(g: HypergraphForCoupling): CoupledEdgeResult[] {
        if (g.isEmpty()) {
            return [];
        }

        const result: CoupledEdgeResult[] = [];
        const minimalFrontiers = g.getMinimalProductiveFrontiers();

        for (const frontier of minimalFrontiers) {
            const expiryEdges = g.getExpiryEdges(frontier);

            if (expiryEdges.length > 0) {
                result.push({
                    type: 'coupled',
                    underlyingEdges: expiryEdges,
                    frontier: frontier,
                    sources: new CoupledEdge(expiryEdges).sources,
                    targets: new CoupledEdge(expiryEdges).targets
                });
            }

            const remainingGraph = g.clone();
            remainingGraph.removeNodes(frontier);
            const recursiveResult = couple(remainingGraph);
            result.push(...recursiveResult);
        }

        return result;
    }

    return couple(graph);
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
    'productive-expiries': {
        name: 'Productive Expiries',
        description: 'Maximal coupling based on minimal productive expiries',
        compute: computeCouplingProductiveExpiries
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

