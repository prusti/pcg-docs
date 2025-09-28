This repository stores documentation on the PCG design and implementation. It is
intended to be the authoritative source on information about the PCG.

These documents are accessible at: https://viperproject.github.io/pcg-docs

## Local Development

Ensure that you have `mdbook`, `mdbook katex`, and Node.js (>=14.0.0) installed:

```
cargo install mdbook
cargo install mdbook-katex
```

The documentation renders hypergraphs using Cytoscape.js. The hypergraph preprocessor requires Node.js to be installed.

If this is your first time setting up the project or if package dependencies have changed, run:
```
npm install
```

Once you have the prerequisites and dependencies installed, run `mdbook serve` from the root directory. The
book should then be hosted on at `http://localhost:3000`

### Hypergraph Support

This documentation includes a custom mdbook preprocessor for rendering hypergraphs. Hypergraphs can be included in markdown files using either JSON or YAML format:

#### JSON Format
````markdown
```hypergraph
{
  "height": "500px",
  "nodes": [
    {"id": "lp1", "place": "x", "lifetime": "'a", "x": 100, "y": 100},
    {"id": "p1", "place": "y", "x": 200, "y": 200},
    {"id": "p2", "place": "z", "x": 300, "y": 150}
  ],
  "edges": [
    {"sources": ["lp1"], "targets": ["p1"], "label": "simple edge"},
    {"sources": ["lp1", "p1"], "targets": ["p2"], "label": "hyperedge"}
  ]
}
```
````

#### YAML Format
````markdown
```hypergraph-yaml
height: 500px
nodes:
  - id: lp1
    place: x
    lifetime: "'a"
    x: 100
    y: 100
  - id: p1
    place: y
    x: 200
    y: 200
  - id: p2
    place: z
    x: 300
    y: 150
edges:
  - sources: [lp1]
    targets: [p1]
    label: simple edge
  - sources: [lp1, p1]
    targets: [p2]
    label: hyperedge
```
````

#### Parameters

- `height` (optional): Controls the height of the rendered graph (default: "400px")

#### Node Types

Nodes in hypergraphs can be one of two types based on their fields:

1. **Lifetime Projection Nodes**: Have both `place` and `lifetime` fields
   - Displayed with hexagonal shape
   - Label format: `place ↓ lifetime`
   - Color: Purple (#673AB7)

2. **Place Nodes**: Have only `place` field (no `lifetime`)
   - Displayed with rounded rectangle shape
   - Label format: `place`
   - Color: Orange (#FF9800)

All nodes require:
- `id`: Unique identifier for the node
- `x`, `y`: Position coordinates
- Either `place` alone (for place nodes) or both `place` and `lifetime` (for lifetime projection nodes)

#### Edge Structure

All edges in the hypergraph are represented uniformly with:
- `sources`: Array of source node IDs
- `targets`: Array of target node IDs
- `label` (optional): Edge label text

Edges are automatically styled as hyperedges when they have multiple sources or targets.


## Deployment

The documentation will automatically be built and deployed upon a push to
`main`. This is implemented via a Github action.
