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

Once you have the prerequisites, run `mdbook serve` from the root directory. The
book should then be hosted on at `http://localhost:3000`

### Hypergraph Support

This documentation includes a custom mdbook preprocessor for rendering hypergraphs. Hypergraphs can be included in markdown files using the following syntax:

````markdown
```hypergraph
{
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


## Deployment

The documentation will automatically be built and deployed upon a push to
`main`. This is implemented via a Github action.
