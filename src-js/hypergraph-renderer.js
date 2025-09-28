import cytoscape from 'cytoscape';
import Layers from 'cytoscape-layers';
import BubbleSets from 'cytoscape-bubblesets';

// Register extensions
cytoscape.use(Layers);
cytoscape.use(BubbleSets);

// Hypergraph renderer
(function() {
    // Wait for page to load
    document.addEventListener('DOMContentLoaded', function() {
        renderAllHypergraphs();
    });

    // Also re-render when navigating between pages in mdbook
    if (typeof window.addEventListener === 'function') {
        window.addEventListener('load', renderAllHypergraphs);

        // Listen for page changes in mdbook
        const observer = new MutationObserver(function(mutations) {
            mutations.forEach(function(mutation) {
                if (mutation.type === 'childList') {
                    setTimeout(renderAllHypergraphs, 100);
                }
            });
        });

        const config = { childList: true, subtree: true };
        observer.observe(document.body, config);
    }

    function renderAllHypergraphs() {
        const containers = document.querySelectorAll('.hypergraph-container');

        containers.forEach(function(container) {
            // Skip if already rendered
            if (container.hasAttribute('data-rendered')) {
                return;
            }

            const dataElement = container.querySelector('.hypergraph-data');
            if (!dataElement) return;

            try {
                const graphData = JSON.parse(dataElement.textContent);
                renderHypergraph(container, graphData);
                container.setAttribute('data-rendered', 'true');
            } catch (e) {
                console.error('Failed to render hypergraph:', e);
                container.innerHTML = '<div class="hypergraph-error">Failed to render graph: ' + e.message + '</div>';
            }
        });
    }

    function renderHypergraph(container, data) {
        // Clear the container
        container.innerHTML = '';

        // Get custom height from container attribute, default to 400px
        const customHeight = container.getAttribute('data-height') || '400px';

        // Create a div for the graph
        const graphDiv = document.createElement('div');
        graphDiv.style.height = customHeight;
        graphDiv.style.width = '100%';
        graphDiv.style.border = '1px solid #ddd';
        graphDiv.style.borderRadius = '4px';
        container.appendChild(graphDiv);

        // Prepare elements for Cytoscape
        const elements = [];
        const hyperedgeGroups = []; // Store hyperedge groupings for bubblesets

        // Add nodes
        if (data.nodes) {
            data.nodes.forEach(function(node) {
                // Determine node type and label based on place/lifetime fields
                let nodeType = 'default';
                let label = node.id;

                if (node.place && !node.lifetime) {
                    // Place node - just show the place
                    nodeType = 'place';
                    label = node.place;
                } else if (node.place && node.lifetime) {
                    // Lifetime projection node - show place ↓ lifetime
                    nodeType = 'lifetimeProjection';
                    label = node.place + ' ↓ ' + node.lifetime;
                } else if (node.label) {
                    // Fallback to provided label
                    label = node.label;
                }

                elements.push({
                    data: {
                        id: node.id,
                        label: label,
                        nodeType: nodeType,
                        place: node.place,
                        lifetime: node.lifetime
                    },
                    position: {
                        x: node.x || Math.random() * 300,
                        y: node.y || Math.random() * 300
                    },
                    classes: nodeType
                });
            });
        }

        // Process edges - create individual edges for all source-target pairs
        if (data.edges) {
            data.edges.forEach(function(edge, idx) {
                const edgeId = edge.id || 'edge-' + idx;

                // Handle edges with sources and targets arrays
                if (edge.sources && edge.targets) {
                    const isHyperedge = edge.sources.length > 1 || edge.targets.length > 1;

                    if (isHyperedge) {
                        // Store hyperedge grouping for bubblesets
                        const group = {
                            id: edgeId,
                            sources: edge.sources,
                            targets: edge.targets,
                            edges: []
                        };

                        // Create individual edges from each source to each target
                        edge.sources.forEach(function(source) {
                            edge.targets.forEach(function(target) {
                                const individualEdgeId = edgeId + '-' + source + '-' + target;
                                group.edges.push(individualEdgeId);
                                elements.push({
                                    data: {
                                        id: individualEdgeId,
                                        source: source,
                                        target: target,
                                        hyperedgeGroup: edgeId
                                    },
                                    classes: 'hyperedge'
                                });
                            });
                        });

                        hyperedgeGroups.push(group);
                    } else {
                        // Simple edge (single source to single target)
                        elements.push({
                            data: {
                                id: edgeId,
                                source: edge.sources[0],
                                target: edge.targets[0]
                            }
                        });
                    }
                } else if (edge.source && edge.target) {
                    // Backward compatibility: handle old format with single source/target
                    elements.push({
                        data: {
                            id: edgeId,
                            source: edge.source,
                            target: edge.target
                        }
                    });
                }
            });
        }

        // Initialize Cytoscape
        const cy = cytoscape({
            container: graphDiv,
            elements: elements,

            style: [
                {
                    selector: 'node',
                    style: {
                        'background-color': '#666',
                        'label': 'data(label)',
                        'text-valign': 'center',
                        'text-halign': 'center',
                        'width': '100px',
                        'height': '40px',
                        'font-size': '12px',
                        'font-family': 'monospace',
                        'color': '#fff',
                        'text-outline-width': 2,
                        'text-outline-color': '#666',
                        'shape': 'ellipse',
                        'z-index': 10
                    }
                },
                {
                    selector: 'node.lifetimeProjection',
                    style: {
                        'background-color': '#673AB7',
                        'text-outline-color': '#673AB7',
                        'shape': 'hexagon',
                        'width': '110px',
                        'height': '35px'
                    }
                },
                {
                    selector: 'node.place',
                    style: {
                        'background-color': '#FF9800',
                        'text-outline-color': '#FF9800',
                        'shape': 'round-rectangle',
                        'width': '80px',
                        'height': '35px'
                    }
                },
                {
                    selector: 'node.input',
                    style: {
                        'background-color': '#4CAF50',
                        'text-outline-color': '#4CAF50',
                        'shape': 'ellipse'
                    }
                },
                {
                    selector: 'node.output',
                    style: {
                        'background-color': '#2196F3',
                        'text-outline-color': '#2196F3',
                        'shape': 'round-rectangle'
                    }
                },
                {
                    selector: 'edge',
                    style: {
                        'width': 3,
                        'line-color': '#999',
                        'target-arrow-color': '#999',
                        'target-arrow-shape': 'triangle',
                        'curve-style': 'bezier',
                        'label': 'data(label)',
                        'font-size': '12px',
                        'text-rotation': 'autorotate',
                        'text-margin-y': -10
                    }
                },
                {
                    selector: 'edge.hyperedge',
                    style: {
                        'line-color': 'rgba(255, 87, 34, 0.3)',
                        'target-arrow-color': 'rgba(255, 87, 34, 0.5)',
                        'width': 2,
                        'line-style': 'dotted',
                        'target-arrow-shape': 'triangle',
                        'z-index': 1
                    }
                }
            ],

            layout: {
                name: data.nodes && data.nodes.some(n => n.x !== undefined && n.y !== undefined) ? 'preset' : 'cose',
                padding: 30,
                // Options for cose layout when positions aren't specified
                idealEdgeLength: 100,
                nodeOverlap: 20,
                refresh: 20,
                fit: true,
                randomize: false,
                componentSpacing: 100,
                nodeRepulsion: 400000,
                edgeElasticity: 100,
                nestingFactor: 5,
                gravity: 80,
                numIter: 1000,
                initialTemp: 200,
                coolingFactor: 0.95,
                minTemp: 1.0
            }
        });

        // Add zoom controls
        const zoomControls = document.createElement('div');
        zoomControls.style.position = 'absolute';
        zoomControls.style.top = '10px';
        zoomControls.style.right = '10px';
        zoomControls.innerHTML = `
            <button onclick="this.parentElement.cy.fit()" style="margin: 2px">Fit</button>
            <button onclick="this.parentElement.cy.zoom(this.parentElement.cy.zoom() * 1.2)" style="margin: 2px">+</button>
            <button onclick="this.parentElement.cy.zoom(this.parentElement.cy.zoom() * 0.8)" style="margin: 2px">-</button>
        `;
        zoomControls.cy = cy;
        graphDiv.style.position = 'relative';
        graphDiv.appendChild(zoomControls);

        // Auto-fit the graph
        cy.fit();

        // Initialize bubblesets
        const bb = cy.bubbleSets();

        // Add bubblesets for each hyperedge group
        hyperedgeGroups.forEach(function(group, idx) {
            // Collect all nodes in this hyperedge
            const nodeIds = [...new Set([...group.sources, ...group.targets])];
            const nodes = cy.nodes().filter(function(node) {
                return nodeIds.includes(node.id());
            });

            // Collect all edges in this hyperedge
            const edges = cy.edges().filter(function(edge) {
                return group.edges.includes(edge.id());
            });

            // Create a bubbleset path
            const color = `hsla(${(idx * 137) % 360}, 70%, 50%, 0.15)`;
            const borderColor = `hsla(${(idx * 137) % 360}, 70%, 50%, 0.6)`;

            bb.addPath(nodes, edges, null, {
                virtualEdges: true,
                style: {
                    fill: color,
                    stroke: borderColor,
                    strokeWidth: 2
                },
                throttle: 10,
                zIndex: -1
            });
        });
    }

    // Export for global access if needed
    window.renderHypergraph = renderHypergraph;
})();
