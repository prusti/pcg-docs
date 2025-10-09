import cytoscape, {
  Core,
  EdgeDefinition,
  NodeDefinition,
  ElementDefinition,
  StylesheetJson,
} from "cytoscape";
import Layers from "cytoscape-layers";
import BubbleSets from "cytoscape-bubblesets";
import {
  COUPLING_ALGORITHMS,
  applyCouplingAlgorithm,
} from "./coupling-algorithms";

// Register extensions
cytoscape.use(Layers);
cytoscape.use(BubbleSets);

interface GraphNode {
  id: string;
  x?: number;
  y?: number;
  place?: string;
  lifetime?: string;
  label?: string;
}

interface GraphEdge {
  id?: string;
  sources?: string[];
  targets?: string[];
  source?: string;
  target?: string;
  label?: string;
  style?: string;
  underlyingEdges?: GraphEdge[];
}

interface GraphData {
  nodes: GraphNode[];
  edges: GraphEdge[];
}

interface HyperedgeGroup {
  id: string;
  sources: string[];
  targets: string[];
  edges: any[];
}

interface RenderResult {
  elements: ElementDefinition[];
  hyperedgeGroups: HyperedgeGroup[];
}
const CYTOSCAPE_STYLES = [
  {
    selector: "node",
    style: {
      "background-color": "#e0e0e0",
      label: "data(label)",
      "text-valign": "center",
      "text-halign": "center",
      width: "100px",
      height: "40px",
      "font-size": "12px",
      "font-family": "monospace",
      color: "#333",
      "text-outline-width": 2,
      "text-outline-color": "#e0e0e0",
      shape: "ellipse",
      "z-index": 10,
      "border-width": 2,
      "border-color": "#999",
    },
  },
  {
    selector: "node.lifetimeProjection",
    style: {
      "background-color": "#fff",
      "text-outline-color": "#fff",
      "border-color": "#000",
      "border-width": 1,
      shape: "hexagon",
      width: "110px",
      height: "35px",
    },
  },
  {
    selector: "node.place",
    style: {
      "background-color": "#ffe0b2",
      "text-outline-color": "#ffe0b2",
      "border-color": "#FF9800",
      shape: "round-rectangle",
      width: "80px",
      height: "35px",
    },
  },
  {
    selector: "node.input",
    style: {
      "background-color": "#c8e6c9",
      "text-outline-color": "#c8e6c9",
      "border-color": "#4CAF50",
      shape: "ellipse",
    },
  },
  {
    selector: "node.output",
    style: {
      "background-color": "#bbdefb",
      "text-outline-color": "#bbdefb",
      "border-color": "#2196F3",
      shape: "round-rectangle",
    },
  },
  {
    selector: "edge",
    style: {
      width: 3,
      "line-color": "#555",
      "target-arrow-color": "#555",
      "target-arrow-shape": "triangle",
      "curve-style": "bezier",
    },
  },
  {
    selector: "edge[label]",
    style: {
      label: "data(label)",
      "font-size": "12px",
      "text-rotation": "none",
      "text-background-color": "#ffffff",
      "text-background-opacity": 1,
      "text-background-padding": "3px",
      "text-border-width": 1,
      "text-border-color": "#ccc",
      "text-border-opacity": 1,
    },
  },
  {
    selector: "edge.hyperedge",
    style: {
      "line-color": "rgba(255, 87, 34, 0.5)",
      "target-arrow-color": "rgba(255, 87, 34, 0.7)",
      width: 2,
      "line-style": "dotted",
      "target-arrow-shape": "triangle",
      "z-index": 1,
    },
  },
];

// Hypergraph renderer
(function () {
  document.addEventListener("DOMContentLoaded", function () {
    renderAllHypergraphs();
  });

  if (typeof window.addEventListener === "function") {
    window.addEventListener("load", renderAllHypergraphs);

    const observer = new MutationObserver(function (mutations) {
      mutations.forEach(function (mutation) {
        if (mutation.type === "childList") {
          setTimeout(renderAllHypergraphs, 100);
        }
      });
    });

    const config = { childList: true, subtree: true };
    observer.observe(document.body, config);
  }

  function renderAllHypergraphs(): void {
    const containers = document.querySelectorAll(".hypergraph-container");

    containers.forEach(function (container) {
      if (container.hasAttribute("data-rendered")) {
        return;
      }

      const dataElement = container.querySelector(".hypergraph-data");
      if (!dataElement) return;

      try {
        const graphData = JSON.parse(
          dataElement.textContent || "{}"
        ) as GraphData;
        renderHypergraph(container as HTMLElement, graphData);
        container.setAttribute("data-rendered", "true");
      } catch (e) {
        console.error("Failed to render hypergraph:", e);
        container.innerHTML =
          '<div class="hypergraph-error">Failed to render graph: ' +
          (e as Error).message +
          "</div>";
      }
    });
  }

  function renderHypergraph(container: HTMLElement, data: GraphData): void {
    container.innerHTML = "";

    const customHeight = container.getAttribute("data-height") || "400px";

    let couplingAlgorithms: string[] = [];
    try {
      const couplingAttr = container.getAttribute("data-coupling-algorithms");
      if (couplingAttr) {
        couplingAlgorithms = JSON.parse(couplingAttr) as string[];
      }
    } catch (e) {
      console.error("Failed to parse coupling algorithms:", e);
    }

    let couplingSelector: HTMLDivElement | null = null;
    if (couplingAlgorithms.length > 0) {
      couplingSelector = document.createElement("div");
      couplingSelector.style.marginBottom = "10px";
      couplingSelector.style.padding = "10px";
      couplingSelector.style.backgroundColor = "#f5f5f5";
      couplingSelector.style.borderRadius = "4px";
      const defaultAlgorithm = couplingAlgorithms[0];
      couplingSelector.innerHTML = `
                <label style="margin-right: 10px; font-weight: bold;">Coupling Algorithm:</label>
                <select id="coupling-select-${container.id}" style="padding: 5px; border-radius: 3px;">
                    <option value="none">None (Original)</option>
                    ${couplingAlgorithms
                      .map((alg) => {
                        const algInfo = COUPLING_ALGORITHMS[alg];
                        const selected = alg === defaultAlgorithm ? ' selected' : '';
                        return `<option value="${alg}"${selected}>${algInfo ? algInfo.name : alg}</option>`;
                      })
                      .join("")}
                </select>
                <span id="coupling-info-${container.id}" style="margin-left: 10px; font-size: 12px; color: #666;"></span>
            `;
      container.appendChild(couplingSelector);
    }

    const graphDiv = document.createElement("div");
    graphDiv.style.height = customHeight;
    graphDiv.style.width = "100%";
    graphDiv.style.border = "1px solid #ccc";
    graphDiv.style.borderRadius = "4px";
    graphDiv.style.backgroundColor = "#fff";
    container.appendChild(graphDiv);

    function processNodes(nodes: GraphNode[]): NodeDefinition[] {
      return nodes.map(function (node) {
        let nodeType = "default";
        let label = node.id;

        if (node.place && !node.lifetime) {
          nodeType = "place";
          label = node.place;
        } else if (node.place && node.lifetime) {
          nodeType = "lifetimeProjection";
          label = node.place + " ↓ " + node.lifetime;
        } else if (node.label) {
          label = node.label;
        }

        return {
          data: {
            id: node.id,
            label: label,
            nodeType: nodeType,
            place: node.place,
            lifetime: node.lifetime,
          },
          position: {
            x: node.x || 0,
            y: node.y || 0,
          },
          classes: nodeType,
        } as NodeDefinition;
      });
    }

    function applyCouplingToEdges(
      edges: GraphEdge[],
      nodes: GraphNode[],
      couplingAlgorithmId: string
    ): GraphEdge[] {
      if (!couplingAlgorithmId || couplingAlgorithmId === "none") {
        return edges;
      }

      try {
        const coupledEdges = applyCouplingAlgorithm(
          couplingAlgorithmId,
          nodes,
          edges
        );
        console.log("coupledEdges", coupledEdges);

        const coupledEdgeObjects = coupledEdges.map(function (coupled, idx) {
          return {
            id: `coupled-${idx}`,
            sources: coupled.sources,
            targets: coupled.targets,
            style: "coupled",
            underlyingEdges: coupled.underlyingEdges,
          };
        });

        const infoSpan = document.getElementById(
          `coupling-info-${container.id}`
        );
        if (infoSpan) {
          infoSpan.textContent = `(${coupledEdges.length} coupled edge${coupledEdges.length !== 1 ? "s" : ""})`;
        }

        return [...edges, ...coupledEdgeObjects];
      } catch (e) {
        console.error("Failed to apply coupling algorithm:", e);
        const infoSpan = document.getElementById(
          `coupling-info-${container.id}`
        );
        if (infoSpan) {
          infoSpan.textContent = `Error: ${(e as Error).message}`;
          infoSpan.style.color = "red";
        }
        return edges;
      }
    }

    function processEdges(edges: GraphEdge[]): {
      edgeElements: EdgeDefinition[];
      hyperedgeGroups: HyperedgeGroup[];
    } {
      const edgeElements: EdgeDefinition[] = [];
      const hyperedgeGroups: HyperedgeGroup[] = [];

      edges.forEach(function (edge, idx) {
        const edgeId = edge.id || "edge-" + idx;

        if (edge.sources && edge.targets) {
          const isMultiSourceOrTarget =
            edge.sources.length > 1 || edge.targets.length > 1;
          const useBubbles = isMultiSourceOrTarget || edge.style === "coupled";

          if (useBubbles) {
            const group: HyperedgeGroup = {
              id: edgeId,
              sources: edge.sources,
              targets: edge.targets,
              edges: [],
            };
            hyperedgeGroups.push(group);
          } else {
            const edgeData: any = {
              id: edgeId,
              source: edge.sources[0],
              target: edge.targets[0],
            };
            if (edge.label) {
              edgeData.label = edge.label;
            }
            edgeElements.push({
              data: edgeData,
            } as EdgeDefinition);
          }
        } else if (edge.source && edge.target) {
          const edgeData: any = {
            id: edgeId,
            source: edge.source,
            target: edge.target,
          };
          if (edge.label) {
            edgeData.label = edge.label;
          }
          edgeElements.push({
            data: edgeData,
          } as EdgeDefinition);
        }
      });

      return { edgeElements, hyperedgeGroups };
    }

    function renderGraph(couplingAlgorithmId: string): RenderResult {
      const nodeElements = processNodes(data.nodes);

      const edgesToRender = applyCouplingToEdges(
        [...data.edges],
        data.nodes,
        couplingAlgorithmId
      );
      console.log("edgesToRender", edgesToRender);

      const { edgeElements, hyperedgeGroups } = processEdges(edgesToRender);

      return {
        elements: [...nodeElements, ...edgeElements],
        hyperedgeGroups,
      };
    }

    const initialAlgorithm = couplingAlgorithms.length > 0 ? couplingAlgorithms[0] : "none";
    let { elements, hyperedgeGroups } = renderGraph(initialAlgorithm);

    const cy = cytoscape({
      container: graphDiv,
      elements: elements,

      style: CYTOSCAPE_STYLES as StylesheetJson,

      layout: {
        name:
          data.nodes &&
          data.nodes.some((n) => n.x !== undefined && n.y !== undefined)
            ? "preset"
            : "cose",
        padding: 30,
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
        minTemp: 1.0,
      },
    });

    const zoomControls = document.createElement("div");
    zoomControls.style.position = "absolute";
    zoomControls.style.top = "10px";
    zoomControls.style.right = "10px";
    zoomControls.innerHTML = `
            <button onclick="this.parentElement.cy.fit()" style="margin: 2px">Fit</button>
            <button onclick="this.parentElement.cy.zoom(this.parentElement.cy.zoom() * 1.2)" style="margin: 2px">+</button>
            <button onclick="this.parentElement.cy.zoom(this.parentElement.cy.zoom() * 0.8)" style="margin: 2px">-</button>
        `;
    (zoomControls as any).cy = cy;
    graphDiv.style.position = "relative";
    graphDiv.appendChild(zoomControls);

    cy.fit();

    const bb = (cy as any).bubbleSets();
    let bubblePaths: any[] = [];

    function renderBubblesets(): void {
      bubblePaths.forEach(function (path) {
        bb.removePath(path);
      });
      bubblePaths = [];

      hyperedgeGroups.forEach(function (group, idx) {
        const nodeIds = [...new Set([...group.sources, ...group.targets])];
        const nodes = cy.nodes().filter(function (node) {
          return nodeIds.includes(node.id());
        });

        const edges = cy.collection();

        const color = `hsla(${(idx * 137) % 360}, 70%, 50%, 0.15)`;
        const borderColor = `hsla(${(idx * 137) % 360}, 70%, 50%, 0.6)`;

        const path = bb.addPath(nodes, edges, null, {
          virtualEdges: true,
          style: {
            fill: color,
            stroke: borderColor,
            strokeWidth: 2,
          },
          throttle: 10,
          zIndex: -1,
        });
        bubblePaths.push(path);
      });
    }

    renderBubblesets();

    if (couplingSelector) {
      const select = document.getElementById(
        `coupling-select-${container.id}`
      ) as HTMLSelectElement;
      if (select) {
        select.addEventListener("change", function () {
          const selectedAlgorithm = select.value;

          cy.elements().remove();

          const result = renderGraph(selectedAlgorithm);
          elements = result.elements;
          hyperedgeGroups = result.hyperedgeGroups;

          cy.add(elements);
          cy.fit();

          renderBubblesets();
        });
      }
    }
  }

  (window as any).renderHypergraph = renderHypergraph;
})();
