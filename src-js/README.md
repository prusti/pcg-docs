# Coupling Algorithms Test Suite

This directory contains the implementation and comprehensive test suite for hypergraph coupling algorithms.

## Files

- `coupling-algorithms.ts` - Implementation of coupling algorithms including the frontier expiries algorithm
- `coupling-algorithms.test.ts` - Comprehensive test suite with 22 tests
- `hypergraph-renderer.ts` - Visualization and rendering for hypergraphs

## Test Coverage

The test suite achieves **92.59% statement coverage** on `coupling-algorithms.ts` and covers:

### 1. Basic Graph Properties
- Leaf node identification
- Blocked node detection
- Descendant computation

### 2. Frontier Detection
- Valid frontier identification
- Complete frontier enumeration
- Frontier closure validation

### 3. Productive Expiries
- Productive expiry detection
- Unblocked node computation
- Minimal productive frontier finding
- Expiry edge computation

### 4. Unblockings
- All unblockings computation
- Unblocking structure validation
- Distinct unblocking filtering

### 5. Effectively Coupled Sets
- Effectively coupled edge set identification
- Cross-reachable graph validation

### 6. Maximally Coupled Sets
- Maximal coupling computation
- Non-subset validation

### 7. Complete Algorithm
- End-to-end frontier expiries algorithm
- Coupled edge structure validation
- Consistency checking

### 8. Edge Cases
- Empty graphs
- Leaf-only graphs
- Single edges

## Test Graph

The tests use the example graph from `coupling.md` section "Defining Coupling Based on an Expires After Relation":

```
Nodes: a, b, c, d, e
Edges:
  e1: a -> c
  e2: b -> c
  e3: a -> d
  e4: b -> d
  e5: b -> e
```

## Expected Output

The frontier expiries algorithm produces:

**Coupled Edge 1:**
- Underlying edges: e1, e2, e3, e4
- Sources: a, b
- Targets: c, d

**Coupled Edge 2:**
- Underlying edges: e5
- Sources: b
- Targets: e

## Running Tests

```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Run tests with coverage report
npm run test:coverage
```

## CI Integration

Tests run automatically on:
- Push to main branch
- Pull requests to main branch

See `.github/workflows/ci.yml` for CI configuration.

## Algorithm Details

The frontier expiries algorithm implements the definition from `coupling.md` lines 243-269:

1. Compute all unblockings (ordered partitions of nodes)
2. Filter to distinct unblockings (remove subsumed ones)
3. Collect all reachable subgraphs
4. Find effectively coupled edge sets (edges that appear together in all reachable graphs)
5. Find maximally coupled sets (not subsets of other effectively coupled sets)

Each step is individually tested to ensure correctness.

