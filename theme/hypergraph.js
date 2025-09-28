// Hypergraph renderer using Cytoscape.js
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

        // Create a div for the graph
        const graphDiv = document.createElement('div');
        graphDiv.style.height = '400px';
        graphDiv.style.width = '100%';
        graphDiv.style.border = '1px solid #ddd';
        graphDiv.style.borderRadius = '4px';
        container.appendChild(graphDiv);

        // Prepare elements for Cytoscape
        const elements = [];

        // Add nodes
        if (data.nodes) {
            data.nodes.forEach(function(node) {
                elements.push({
                    data: {
                        id: node.id,
                        label: node.label || node.id,
                        nodeType: node.type || 'default'
                    },
                    position: {
                        x: node.x || Math.random() * 300,
                        y: node.y || Math.random() * 300
                    },
                    classes: node.type || 'default'
                });
            });
        }

        // Add regular edges
        if (data.edges) {
            data.edges.forEach(function(edge, idx) {
                elements.push({
                    data: {
                        id: 'edge-' + idx,
                        source: edge.source,
                        target: edge.target,
                        label: edge.label || ''
                    }
                });
            });
        }

        // Add hyperedges (visualized as compound nodes)
        if (data.hyperedges) {
            data.hyperedges.forEach(function(hyperedge) {
                // Create a compound node for the hyperedge
                const heId = hyperedge.id || 'he-' + Math.random();

                // Add hyperedge as a styled edge group
                if (hyperedge.sources && hyperedge.targets) {
                    hyperedge.sources.forEach(function(source) {
                        hyperedge.targets.forEach(function(target) {
                            elements.push({
                                data: {
                                    id: heId + '-' + source + '-' + target,
                                    source: source,
                                    target: target,
                                    label: hyperedge.label || '',
                                    hyperedge: true,
                                    coupled: hyperedge.coupled || false
                                },
                                classes: 'hyperedge' + (hyperedge.coupled ? ' coupled' : '')
                            });
                        });
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
                        'width': '60px',
                        'height': '60px',
                        'font-size': '14px',
                        'color': '#fff',
                        'text-outline-width': 2,
                        'text-outline-color': '#666'
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
                        'line-color': '#FF5722',
                        'target-arrow-color': '#FF5722',
                        'width': 4,
                        'line-style': 'dashed'
                    }
                },
                {
                    selector: 'edge.coupled',
                    style: {
                        'line-color': '#9C27B0',
                        'target-arrow-color': '#9C27B0',
                        'width': 5,
                        'line-style': 'solid'
                    }
                }
            ],

            layout: {
                name: 'preset',
                padding: 30
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
    }
})();
