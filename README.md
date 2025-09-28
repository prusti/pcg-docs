# PCG Documentation

This repository contains documentation on the PCG design and implementation. It
is intended to be the authoritative source on information about the PCG.
However, because much of the documentation is still incomplete or outdated, the
paper describing the PCG is probably a better resource currently:
https://arxiv.org/pdf/2503.21691.


**Live documentation**: https://viperproject.github.io/pcg-docs

## Quick Start

### Prerequisites

- **Node.js** (>= 14.0.0) - [Install from nodejs.org](https://nodejs.org/)
- **Rust** (for mdbook) - [Install from rust-lang.org](https://www.rust-lang.org/tools/install)

### Setup

First-time setup installs all dependencies including mdbook and mdbook-katex:

```bash
make setup
```

This command will:
- Install dependencies (Cytoscape.js, webpack, etc.)
- Install mdbook and mdbook-katex via cargo

### Development

Start the development server with automatic reload on changes:

```bash
make serve
```

This will:
- Build the JavaScript bundle
- Start watching for JavaScript changes
- Start mdbook server at http://localhost:3000
- Automatically rebuild on any source file changes

### Build for Production

Build the static site for deployment:

```bash
make build
```

This creates the production-ready site in the `book/` directory.

### Available Commands

| Command | Description |
|---------|-------------|
| `make setup` | One-time setup: installs all dependencies |
| `make serve` | Start development server with auto-reload |
| `make build` | Build production site |
| `make clean` | Remove generated files and dependencies |
| `make help` | Show available commands |

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

#### Hyperedge Visualization

Hyperedges (edges with multiple sources or targets) are visualized using the cytoscape-bubblesets library:
- Individual edges are drawn between all source-target pairs with dotted lines
- A colored bubble overlay groups all nodes participating in the hyperedge
- Each hyperedge gets a unique color for its bubble
- Bubbles can overlap, allowing nodes to belong to multiple hyperedges


## Deployment

The documentation is automatically built and deployed to GitHub Pages when changes are pushed to the `main` branch.

## Technical Details

### Architecture

The documentation system consists of:
- **mdbook**: Static site generator for the main documentation
- **mdbook-katex**: LaTeX math rendering support
- **Custom preprocessor**: Converts hypergraph code blocks to interactive visualizations
- **Cytoscape.js**: Graph visualization library
- **cytoscape-bubblesets**: Plugin for visualizing hyperedges as bubble overlays
- **Webpack**: Bundles JavaScript dependencies into a single file

### Build Process

1. **Preprocessing**: The hypergraph preprocessor (`preprocessors/hypergraph.js`) converts graph definitions in markdown to HTML containers
2. **JavaScript bundling**: Webpack bundles the renderer and dependencies into `theme/hypergraph.js`
3. **Site generation**: mdbook processes markdown files and generates the static HTML site
4. **Runtime rendering**: The bundled JavaScript renders interactive graphs in the browser

### Project Structure

```
pcg-docs/
├── src/                 # Markdown source files
├── src-js/              # JavaScript source for hypergraph renderer
├── preprocessors/       # mdbook preprocessors
├── theme/              # CSS and bundled JavaScript
├── scripts/            # Build and setup scripts
├── book/               # Generated static site (not stored in version control)
└── webpack.config.js   # Webpack bundling configuration
```
