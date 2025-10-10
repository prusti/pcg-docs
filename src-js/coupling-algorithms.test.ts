/**
 * Test suite for coupling algorithms
 *
 * These tests verify each step of the unblocking frontier expiries algorithm
 * using the example graph from "Defining Coupling Based on an Expires After Relation"
 * in coupling.md
 */

import { applyCouplingAlgorithm } from "./coupling-algorithms";

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

describe("Coupling Algorithms - Test Graph from coupling.md", () => {
  const testNodes: Node[] = [
    { id: "a" },
    { id: "b" },
    { id: "c" },
    { id: "d" },
    { id: "e" },
  ];

  const testEdges: Edge[] = [
    { id: "ac", sources: ["a"], targets: ["c"] },
    { id: "bc", sources: ["b"], targets: ["c"] },
    { id: "ad", sources: ["a"], targets: ["d"] },
    { id: "bd", sources: ["b"], targets: ["d"] },
    { id: "be", sources: ["b"], targets: ["e"] },
  ];

  describe("Basic Graph Properties", () => {
    test("should identify leaf nodes correctly", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const leaves = graph.getLeafNodes();
      expect(leaves).toEqual(new Set(["c", "d", "e"]));
    });

    test("should identify blocked nodes correctly", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const blocked = graph.getBlockedNodes();
      expect(blocked.sort()).toEqual(["a", "b"]);
    });

    test("should compute descendants correctly", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const descendantsOfA = graph.getDescendants("a");
      expect(descendantsOfA).toEqual(new Set(["a", "c", "d"]));

      const descendantsOfB = graph.getDescendants("b");
      expect(descendantsOfB).toEqual(new Set(["b", "c", "d", "e"]));
    });
  });

  describe("Frontier Detection", () => {
    test("should identify valid frontiers", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      expect(graph.isFrontier(["c", "d"])).toBe(true);
      expect(graph.isFrontier(["c", "d", "e"])).toBe(true);
      expect(graph.isFrontier(["a", "c", "d"])).toBe(true);
      expect(graph.isFrontier(["d"])).toBe(true);
      expect(graph.isFrontier(["c"])).toBe(true);
      expect(graph.isFrontier(["e"])).toBe(true);

      expect(graph.isFrontier(["a"])).toBe(false);
      expect(graph.isFrontier(["b"])).toBe(false);
    });

    test("should compute all frontiers", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const frontiers = graph.getAllFrontiers();

      expect(frontiers.length).toBeGreaterThan(0);
      frontiers.forEach((frontier: string[]) => {
        expect(graph.isFrontier(frontier)).toBe(true);
      });
    });
  });

  describe("Productive Expiries", () => {
    test("should identify productive expiries", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      expect(graph.isProductiveExpiry(["c", "d"])).toBe(true);

      const unblockedByCd = graph.getUnblockedNodes(["c", "d"]);
      expect(unblockedByCd).toContain("a");

      expect(graph.isProductiveExpiry(["c", "d", "e"])).toBe(true);
      const unblockedByCde = graph.getUnblockedNodes(["c", "d", "e"]);
      expect(unblockedByCde.sort()).toEqual(["a", "b"]);
    });

    test("should compute minimal productive frontiers", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const minimalFrontiers = graph.getMinimalProductiveFrontiers();

      expect(minimalFrontiers.length).toBeGreaterThan(0);
      minimalFrontiers.forEach((frontier: string[]) => {
        expect(graph.isProductiveExpiry(frontier)).toBe(true);
      });
    });

    test("should compute expiry edges correctly", () => {
      const { HypergraphForCoupling } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const expiryEdges = graph.getExpiryEdges(["c", "d"]);
      const edgeIds = expiryEdges.map((e: any) => e.id).sort();

      expect(edgeIds).toEqual(["ac", "ad", "bc", "bd"]);
    });
  });

  describe("Unblockings", () => {
    test("should compute all unblockings", () => {
      const {
        computeAllUnblockings,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const unblockings = computeAllUnblockings(graph);

      expect(unblockings.length).toBeGreaterThan(0);

      unblockings.forEach((unblocking: any) => {
        expect(unblocking.partitions).toBeDefined();
        expect(unblocking.reachableGraphs).toBeDefined();
        expect(unblocking.partitions.length).toBeGreaterThan(0);
        expect(unblocking.reachableGraphs.length).toBe(
          unblocking.partitions.length + 1
        );
      });
    });

    test("unblockings should have valid structure", () => {
      const {
        computeAllUnblockings,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const unblockings = computeAllUnblockings(graph);

      unblockings.forEach((unblocking: any) => {
        const firstPartition = unblocking.partitions[0];
        expect(firstPartition.length).toBeGreaterThan(0);

        const firstGraph = unblocking.reachableGraphs[0];
        expect(firstGraph).toBeDefined();

        firstPartition.forEach((node: string) => {
          expect(firstGraph.nodes.has(node)).toBe(true);
        });
      });
    });

    test("should filter to distinct unblockings", () => {
      const {
        computeAllUnblockings,
        getDistinctUnblockings,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const allUnblockings = computeAllUnblockings(graph);
      const distinctUnblockings = getDistinctUnblockings(allUnblockings);

      expect(distinctUnblockings.length).toBeLessThanOrEqual(
        allUnblockings.length
      );
      expect(distinctUnblockings.length).toBeGreaterThan(0);
    });
  });

  describe("Effectively Coupled Sets", () => {
    test("should find effectively coupled edge sets", () => {
      const {
        computeAllUnblockings,
        getDistinctUnblockings,
        findEffectivelyCoupledSets,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const allUnblockings = computeAllUnblockings(graph);
      const distinctUnblockings = getDistinctUnblockings(allUnblockings);

      const reachableGraphs: any[] = [];
      for (const unblocking of distinctUnblockings) {
        for (const g of unblocking.reachableGraphs) {
          reachableGraphs.push(g);
        }
      }

      const edgeIds = graph.edges.map((e: any) => e.id);
      const effectivelyCoupled = findEffectivelyCoupledSets(
        reachableGraphs,
        edgeIds
      );

      expect(effectivelyCoupled.length).toBeGreaterThan(0);

      effectivelyCoupled.forEach((edgeSet: Set<string>) => {
        expect(edgeSet.size).toBeGreaterThan(0);
        expect(edgeSet.size).toBeLessThanOrEqual(5);
      });
    });

    test("effectively coupled sets should appear together in all reachable graphs", () => {
      const {
        computeAllUnblockings,
        getDistinctUnblockings,
        findEffectivelyCoupledSets,
        isEffectivelyCoupled,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const allUnblockings = computeAllUnblockings(graph);
      const distinctUnblockings = getDistinctUnblockings(allUnblockings);

      const reachableGraphs: any[] = [];
      for (const unblocking of distinctUnblockings) {
        for (const g of unblocking.reachableGraphs) {
          reachableGraphs.push(g);
        }
      }

      const edgeIds = graph.edges.map((e: any) => e.id);
      const effectivelyCoupled = findEffectivelyCoupledSets(
        reachableGraphs,
        edgeIds
      );

      effectivelyCoupled.forEach((edgeSet: Set<string>) => {
        const edgeArray = Array.from(edgeSet);
        expect(isEffectivelyCoupled(edgeArray, reachableGraphs)).toBe(true);
      });
    });
  });

  describe("Maximally Coupled Sets", () => {
    test("should find maximally coupled sets", () => {
      const {
        computeAllUnblockings,
        getDistinctUnblockings,
        findEffectivelyCoupledSets,
        findMaximallyCoupledSets,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const allUnblockings = computeAllUnblockings(graph);
      const distinctUnblockings = getDistinctUnblockings(allUnblockings);

      const reachableGraphs: any[] = [];
      for (const unblocking of distinctUnblockings) {
        for (const g of unblocking.reachableGraphs) {
          reachableGraphs.push(g);
        }
      }

      const edgeIds = graph.edges.map((e: any) => e.id);
      const effectivelyCoupled = findEffectivelyCoupledSets(
        reachableGraphs,
        edgeIds
      );
      const maximallyCoupled = findMaximallyCoupledSets(effectivelyCoupled);

      expect(maximallyCoupled.length).toBeGreaterThan(0);
      expect(maximallyCoupled.length).toBeLessThanOrEqual(
        effectivelyCoupled.length
      );
    });

    test("maximally coupled sets should not be subsets of each other", () => {
      const {
        computeAllUnblockings,
        getDistinctUnblockings,
        findEffectivelyCoupledSets,
        findMaximallyCoupledSets,
        HypergraphForCoupling,
      } = require("./coupling-algorithms");
      const graph = new HypergraphForCoupling(testNodes, testEdges);

      const allUnblockings = computeAllUnblockings(graph);
      const distinctUnblockings = getDistinctUnblockings(allUnblockings);

      const reachableGraphs: any[] = [];
      for (const unblocking of distinctUnblockings) {
        for (const g of unblocking.reachableGraphs) {
          reachableGraphs.push(g);
        }
      }

      const edgeIds = graph.edges.map((e: any) => e.id);
      const effectivelyCoupled = findEffectivelyCoupledSets(
        reachableGraphs,
        edgeIds
      );
      const maximallyCoupled = findMaximallyCoupledSets(effectivelyCoupled);

      for (let i = 0; i < maximallyCoupled.length; i++) {
        for (let j = 0; j < maximallyCoupled.length; j++) {
          if (i === j) continue;

          const set1 = maximallyCoupled[i];
          const set2 = maximallyCoupled[j];

          const set1IsSubsetOfSet2 = Array.from(set1).every((id) =>
            set2.has(id)
          );
          expect(set1IsSubsetOfSet2).toBe(false);
        }
      }
    });
  });

  describe("Complete Frontier Expiries Algorithm", () => {
    test("should produce coupled edges", () => {
      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        testNodes,
        testEdges
      );

      expect(result).toBeDefined();
      expect(Array.isArray(result)).toBe(true);
      expect(result.length).toBeGreaterThan(0);
    });

    test("should document the expected coupled edges for the test graph", () => {
      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        testNodes,
        testEdges
      );

      console.log("\n=== Coupled Edges for Test Graph ===");
      result.forEach((coupled, idx) => {
        const edgeIds = coupled.underlyingEdges.map((e) => e.id).sort();
        console.log(`Coupled Edge ${idx + 1}:`);
        console.log(`  Underlying edges: ${edgeIds.join(", ")}`);
        console.log(`  Sources: ${coupled.sources.sort().join(", ")}`);
        console.log(`  Targets: ${coupled.targets.sort().join(", ")}`);
      });
      console.log("=====================================\n");

      expect(result.length).toBeGreaterThan(0);

      const allUnderlyingEdgeIds = new Set<string>();
      result.forEach((coupled) => {
        coupled.underlyingEdges.forEach((e) => {
          allUnderlyingEdgeIds.add(e.id);
        });
      });

      expect(allUnderlyingEdgeIds.size).toBeGreaterThanOrEqual(1);
    });

    test("coupled edges should have valid structure", () => {
      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        testNodes,
        testEdges
      );

      result.forEach((coupled) => {
        expect(coupled.type).toBe("coupled");
        expect(coupled.underlyingEdges).toBeDefined();
        expect(coupled.underlyingEdges.length).toBeGreaterThan(0);
        expect(coupled.sources).toBeDefined();
        expect(coupled.targets).toBeDefined();
        expect(Array.isArray(coupled.sources)).toBe(true);
        expect(Array.isArray(coupled.targets)).toBe(true);
      });
    });

    test("coupled edges should be consistent with underlying edges", () => {
      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        testNodes,
        testEdges
      );

      result.forEach((coupled) => {
        const allSources = new Set<string>();
        const allTargets = new Set<string>();

        coupled.underlyingEdges.forEach((edge) => {
          edge.sources.forEach((s) => allSources.add(s));
          edge.targets.forEach((t) => allTargets.add(t));
        });

        const expectedSources = Array.from(allSources)
          .filter((s) => !allTargets.has(s))
          .sort();
        const expectedTargets = Array.from(allTargets)
          .filter((t) => !allSources.has(t))
          .sort();

        expect(coupled.sources.sort()).toEqual(expectedSources);
        expect(coupled.targets.sort()).toEqual(expectedTargets);
      });
    });

    test("should produce different results than identity coupling", () => {
      const frontierResult = applyCouplingAlgorithm(
        "frontier-expiries",
        testNodes,
        testEdges
      );
      const identityResult = applyCouplingAlgorithm(
        "none",
        testNodes,
        testEdges
      );

      expect(frontierResult.length).not.toBe(identityResult.length);
    });
  });

  describe("Edge Case Handling", () => {
    test("should handle empty graph", () => {
      const emptyResult = applyCouplingAlgorithm("frontier-expiries", [], []);
      expect(emptyResult).toEqual([]);
    });

    test("should handle graph with only leaf nodes", () => {
      const leafNodes: Node[] = [
        { id: "x", place: "x" },
        { id: "y", place: "y" },
      ];
      const noEdges: Edge[] = [];

      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        leafNodes,
        noEdges
      );
      expect(result).toEqual([]);
    });

    test("should handle single edge", () => {
      const simpleNodes: Node[] = [
        { id: "a", place: "a" },
        { id: "b", place: "b" },
      ];
      const singleEdge: Edge[] = [{ id: "e1", sources: ["a"], targets: ["b"] }];

      const result = applyCouplingAlgorithm(
        "frontier-expiries",
        simpleNodes,
        singleEdge
      );
      expect(result).toBeDefined();
    });
  });
});
