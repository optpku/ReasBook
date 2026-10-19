(function () {
  "use strict";

  var SVG_NS = "http://www.w3.org/2000/svg";
  var NODE_WIDTH = 146;
  var NODE_HEIGHT = 38;
  var LEVEL_GAP = 58;
  var ROW_GAP = 14;
  var MIN_ZOOM = 0.035;
  var MAX_ZOOM = 5;

  var refs = {
    appShell: document.getElementById("appShell"),
    sidebarToggle: document.getElementById("sidebarToggle"),
    detailToggle: document.getElementById("detailToggle"),
    brandMark: document.getElementById("brandMark"),
    projectName: document.getElementById("projectName"),
    searchInput: document.getElementById("searchInput"),
    sectionFilter: document.getElementById("sectionFilter"),
    typeFilter: document.getElementById("typeFilter"),
    indexMeta: document.getElementById("indexMeta"),
    itemList: document.getElementById("itemList"),
    currentLabel: document.getElementById("currentLabel"),
    currentTitle: document.getElementById("currentTitle"),
    fullGraphButton: document.getElementById("fullGraphButton"),
    focusGraphButton: document.getElementById("focusGraphButton"),
    graphDepthSelect: document.getElementById("graphDepthSelect"),
    zoomOutButton: document.getElementById("zoomOutButton"),
    fitButton: document.getElementById("fitButton"),
    zoomInButton: document.getElementById("zoomInButton"),
    graphZoomSlider: document.getElementById("graphZoomSlider"),
    graphZoomValue: document.getElementById("graphZoomValue"),
    mobileGraphButton: document.getElementById("mobileGraphButton"),
    mobileDetailButton: document.getElementById("mobileDetailButton"),
    workspace: document.getElementById("workspace"),
    graphStats: document.getElementById("graphStats"),
    graphViewport: document.getElementById("graphViewport"),
    dependencyGraph: document.getElementById("dependencyGraph"),
    graphScene: document.getElementById("graphScene"),
    graphEmpty: document.getElementById("graphEmpty"),
    legend: document.getElementById("legend"),
    detailContent: document.getElementById("detailContent"),
    fatalError: document.getElementById("fatalError")
  };

  var data = null;
  var project = null;
  var items = [];
  var sections = [];
  var itemById = new Map();
  var sectionById = new Map();
  var orderById = new Map();
  var consumersById = new Map();
  var preferencePrefix = "reasbook-theorem-map";
  var state = {
    selectedId: "",
    graphMode: "focus",
    graphDepth: 3,
    dependencyMode: "all",
    layoutMode: "natural",
    graphviz: null,
    graphvizPromise: null,
    vizScriptPromise: null,
    renderToken: 0,
    sidebarCollapsed: false,
    detailCollapsed: false,
    mobileView: "graph",
    visibleListIds: [],
    transform: { x: 0, y: 0, scale: 1 },
    graphWidth: 1,
    graphHeight: 1,
    pointer: null
  };

  function svgElement(name, attributes) {
    var element = document.createElementNS(SVG_NS, name);
    Object.keys(attributes || {}).forEach(function (key) {
      element.setAttribute(key, String(attributes[key]));
    });
    return element;
  }

  function readPreference(key) {
    try {
      return window.localStorage.getItem(preferencePrefix + ":" + key);
    } catch (error) {
      return null;
    }
  }

  function writePreference(key, value) {
    try {
      window.localStorage.setItem(preferencePrefix + ":" + key, value);
    } catch (error) {
      // Preferences are optional in private and file contexts.
    }
  }

  function sectionMeta(sectionId) {
    return sectionById.get(sectionId) || {
      id: sectionId,
      label: sectionId || "Overview",
      short: sectionId || "Overview",
      color: "#315fb5",
      wash: "#e9effa"
    };
  }

  function applySectionStyle(element, sectionId) {
    var section = sectionMeta(sectionId);
    element.style.setProperty("--section-color", section.color || "#315fb5");
    element.style.setProperty("--section-wash", section.wash || "#e9effa");
  }

  function selectedItem() {
    return itemById.get(state.selectedId) || items[0] || null;
  }

  function itemSort(leftId, rightId) {
    return (orderById.get(leftId) || 0) - (orderById.get(rightId) || 0);
  }

  function directionalNeighborhood(startId, neighbors, maxDepth, allowedIds) {
    // Breadth-first traversal gives shortest hop distance even with cycles.
    // Traverse each direction separately: sharing a prerequisite does not make
    // a sibling declaration part of the selected declaration's neighborhood.
    var result = new Set();
    var visited = new Set([startId]);
    var frontier = [startId];
    var limit = maxDepth === undefined ? Infinity : maxDepth;
    for (var depth = 0; frontier.length && depth < limit; depth += 1) {
      var next = [];
      frontier.forEach(function (id) {
        neighbors(id).forEach(function (neighbor) {
          if (visited.has(neighbor) || !itemById.has(neighbor) ||
              (allowedIds && !allowedIds.has(neighbor))) return;
          visited.add(neighbor);
          result.add(neighbor);
          next.push(neighbor);
        });
      });
      frontier = next;
    }
    return result;
  }

  function ancestorsOf(startId, maxDepth, allowedIds, mode) {
    return directionalNeighborhood(startId, function (id) {
      var item = itemById.get(id);
      return item ? graphTraversalDependencies(item, mode) : [];
    }, maxDepth, allowedIds);
  }

  function descendantsOf(startId, maxDepth, allowedIds, mode) {
    return directionalNeighborhood(startId, function (id) {
      return graphConsumers(id, true, mode);
    }, maxDepth, allowedIds);
  }

  function graphDependencies(item, mode) {
    mode = mode || state.dependencyMode;
    if (mode === "statement" || mode === "statement-edges") return item.statementDependencies || [];
    if (mode === "proof") return item.proofDependencies || [];
    if (mode === "union") return Array.from(new Set((item.statementDependencies || []).concat(item.proofDependencies || [])));
    return item.dependencies;
  }

  function graphTraversalDependencies(item, mode) {
    mode = mode || state.dependencyMode;
    return graphDependencies(item, mode === "statement-edges" ? "union" : mode);
  }

  function graphConsumers(id, traversal, mode) {
    return (consumersById.get(id) || []).filter(function (consumer) {
      var dependencies = traversal ? graphTraversalDependencies(itemById.get(consumer), mode) : graphDependencies(itemById.get(consumer), mode);
      return dependencies.indexOf(id) >= 0;
    });
  }

  function encodePath(path) {
    return String(path || "")
      .split("/")
      .filter(Boolean)
      .map(function (segment) { return encodeURIComponent(segment); })
      .join("/");
  }

  function sourceUrl(item) {
    var repository = String(project.repository || "").replace(/\/$/, "");
    var sourceRoot = encodePath(project.sourceRoot || "");
    var file = encodePath(item.file || "");
    return repository + "/blob/" + encodeURIComponent(project.commit) + "/" +
      sourceRoot + (sourceRoot ? "/" : "") + file +
      "?plain=1#L" + Number(item.line || 1);
  }

  function moduleName(item) {
    if (item.module) {
      return item.module;
    }
    var suffix = String(item.file || "")
      .replace(/\.lean$/, "")
      .replace(/\//g, ".");
    return project.id + (suffix ? "." + suffix : "");
  }

  function populateFilters() {
    sections.forEach(function (section) {
      var option = document.createElement("option");
      option.value = section.id;
      option.textContent = section.label;
      refs.sectionFilter.appendChild(option);
    });
    Array.from(new Set(items.map(function (item) { return item.type; })))
      .sort()
      .forEach(function (type) {
        var option = document.createElement("option");
        option.value = type.toLowerCase();
        option.textContent = type;
        refs.typeFilter.appendChild(option);
      });
  }

  function renderLegend() {
    var fragment = document.createDocumentFragment();
    [
      ["Statement edge", "statement"],
      ["Proof/body edge", "proof"],
      ["Both", "both"],
      [data.generation && /^curated/.test(data.generation.mode || "") ? "Curated" : "Legacy", "unclassified"]
    ].forEach(function (entry) {
      var edgeEntry = document.createElement("span");
      var line = document.createElement("i");
      line.className = "legend-edge legend-edge-" + entry[1];
      edgeEntry.appendChild(line);
      edgeEntry.appendChild(document.createTextNode(entry[0]));
      fragment.appendChild(edgeEntry);
    });
    if (items.some(function (item) { return item.dependencyEvidence === "source-only"; })) {
      var sourceEntry = document.createElement("span");
      var sourceSwatch = document.createElement("i");
      sourceSwatch.className = "legend-source-only";
      sourceEntry.appendChild(sourceSwatch);
      sourceEntry.appendChild(document.createTextNode("Source inventory only"));
      fragment.appendChild(sourceEntry);
    }
    sections.slice(0, 8).forEach(function (section) {
      var entry = document.createElement("span");
      var swatch = document.createElement("i");
      swatch.className = "legend-swatch";
      applySectionStyle(swatch, section.id);
      entry.appendChild(swatch);
      entry.appendChild(document.createTextNode(section.short || section.label));
      fragment.appendChild(entry);
    });
    refs.legend.replaceChildren(fragment);
  }

  function listMatches(item) {
    var needle = refs.searchInput.value.trim().toLowerCase();
    var section = refs.sectionFilter.value;
    var type = refs.typeFilter.value;
    if (section !== "all" && item.section !== section) {
      return false;
    }
    if (type !== "all" && item.type.toLowerCase() !== type) {
      return false;
    }
    if (!needle) {
      return true;
    }
    return [
      item.label,
      item.title,
      item.type,
      item.file,
      item.declaration,
      sectionMeta(item.section).label
    ].join(" ").toLowerCase().indexOf(needle) >= 0;
  }

  function renderList() {
    var visible = items.filter(listMatches);
    var fragment = document.createDocumentFragment();
    refs.itemList.replaceChildren();
    state.visibleListIds = visible.map(function (item) { return item.id; });
    refs.indexMeta.textContent = visible.length + " of " + items.length + " literature items";

    if (!visible.length) {
      var empty = document.createElement("div");
      empty.className = "empty-list";
      empty.textContent = "No literature items match the current filters.";
      refs.itemList.appendChild(empty);
      return;
    }

    sections.forEach(function (section) {
      var sectionItems = visible.filter(function (item) {
        return item.section === section.id;
      });
      if (!sectionItems.length) {
        return;
      }
      var heading = document.createElement("div");
      heading.className = "list-section-label";
      heading.textContent = section.label;
      fragment.appendChild(heading);

      sectionItems.forEach(function (item) {
        var row = document.createElement("button");
        row.type = "button";
        row.className = "item-row";
        row.dataset.itemId = item.id;
        row.setAttribute("role", "option");
        row.setAttribute("aria-selected", String(item.id === state.selectedId));
        applySectionStyle(row, item.section);
        if (item.dependencyEvidence === "source-only") {
          row.classList.add("source-only");
          row.title = "Source inventory only; compiled dependency evidence is unavailable.";
        }
        if (item.id === state.selectedId) {
          row.classList.add("active");
        }

        var label = document.createElement("span");
        label.className = "item-row-label";
        label.textContent = item.label;
        var copy = document.createElement("span");
        copy.className = "item-row-copy";
        var title = document.createElement("span");
        title.className = "item-row-title";
        title.textContent = item.title;
        var declaration = document.createElement("span");
        declaration.className = "item-row-decl";
        declaration.textContent = item.declaration;
        copy.appendChild(title);
        copy.appendChild(declaration);
        row.appendChild(label);
        row.appendChild(copy);
        fragment.appendChild(row);
      });
    });
    refs.itemList.appendChild(fragment);
  }

  function graphVisibleIds(mode) {
    mode = mode || state.dependencyMode;
    var section = refs.sectionFilter.value;
    var result = new Set();
    if (state.graphMode === "focus") {
      if (state.selectedId) {
        result.add(state.selectedId);
        ancestorsOf(state.selectedId, state.graphDepth, undefined, mode).forEach(function (id) { result.add(id); });
        descendantsOf(state.selectedId, state.graphDepth, undefined, mode).forEach(function (id) { result.add(id); });
      }
      return Array.from(result).sort(itemSort);
    }
    if (section === "all") {
      if (mode === "all") return items.map(function (item) { return item.id; });
      // Full means all matching relationships, not unrelated isolated nodes.
      items.forEach(function (item) {
        graphTraversalDependencies(item, mode).forEach(function (dependency) {
          result.add(item.id); result.add(dependency);
        });
      });
      if (state.selectedId) result.add(state.selectedId);
      return Array.from(result).sort(itemSort);
    }
    items.forEach(function (item) {
      if (item.section === section) {
        result.add(item.id);
        ancestorsOf(item.id, undefined, undefined, mode).forEach(function (id) { result.add(id); });
      }
    });
    return Array.from(result).sort(itemSort);
  }

  function graphModel(ids, mode) {
    var idSet = new Set(ids);
    var edges = [];
    ids.forEach(function (targetId) {
      var item = itemById.get(targetId);
      graphDependencies(item, mode).forEach(function (sourceId) {
        if (idSet.has(sourceId)) {
          var inStatement = item.statementDependencies.indexOf(sourceId) >= 0;
          var inProof = item.proofDependencies.indexOf(sourceId) >= 0;
          var kind = inStatement && inProof ? "both" :
            (inStatement ? "statement" : (inProof ? "proof" : "unclassified"));
          edges.push({
            source: sourceId,
            target: targetId,
            id: sourceId + "->" + targetId,
            kind: kind
          });
        }
      });
    });
    return { ids: ids, edges: edges };
  }

  function graphLayoutModel(model) {
    // Both views use one bounded reference geometry; filtering must not move nodes.
    if (state.dependencyMode === "proof" || state.dependencyMode === "statement-edges") {
      return graphModel(graphVisibleIds("statement-edges"), "union");
    }
    return model;
  }

  function graphLayout(model) {
    var ids = model.ids;
    var consumers = new Map(ids.map(function (id) { return [id, []]; }));
    var indegree = new Map();
    var levels = new Map();
    var queue = [];
    ids.forEach(function (id) {
      indegree.set(id, 0);
      levels.set(id, 0);
    });
    model.edges.forEach(function (edge) {
      consumers.get(edge.source).push(edge.target);
      indegree.set(edge.target, indegree.get(edge.target) + 1);
    });
    ids.forEach(function (id) { if (!indegree.get(id)) queue.push(id); });
    queue.sort(itemSort);
    while (queue.length) {
      var current = queue.shift();
      consumers.get(current).forEach(function (consumer) {
        levels.set(consumer, Math.max(levels.get(consumer) || 0, (levels.get(current) || 0) + 1));
        indegree.set(consumer, (indegree.get(consumer) || 1) - 1);
        if (indegree.get(consumer) === 0) {
          queue.push(consumer);
          queue.sort(itemSort);
        }
      });
    }

    var groups = new Map();
    var maximumLevel = 0;
    ids.forEach(function (id) {
      var level = levels.get(id) || 0;
      maximumLevel = Math.max(maximumLevel, level);
      if (!groups.has(level)) {
        groups.set(level, []);
      }
      groups.get(level).push(id);
    });
    groups.forEach(function (group) { group.sort(itemSort); });
    var maximumRows = 1;
    groups.forEach(function (group) { maximumRows = Math.max(maximumRows, group.length); });
    var width = 80 + (maximumLevel + 1) * NODE_WIDTH + maximumLevel * LEVEL_GAP;
    var height = Math.max(390, 70 + maximumRows * NODE_HEIGHT + (maximumRows - 1) * ROW_GAP);
    var positions = new Map();
    groups.forEach(function (group, level) {
      var groupHeight = group.length * NODE_HEIGHT + Math.max(0, group.length - 1) * ROW_GAP;
      var startY = Math.max(35, (height - groupHeight) / 2);
      group.forEach(function (id, row) {
        positions.set(id, {
          x: 40 + level * (NODE_WIDTH + LEVEL_GAP),
          y: startY + row * (NODE_HEIGHT + ROW_GAP)
        });
      });
    });
    return { positions: positions, width: width, height: height };
  }

  function escapeReviewerDot(value) {
    return String(value)
      .replace(/\\/g, "\\\\")
      .replace(/"/g, '\\"')
      .replace(/\r?\n/g, "\\n");
  }

  function reviewerGraphDomId(value) {
    return String(value).replace(/[^a-z0-9_-]+/gi, "-");
  }

  function reviewerGraphHighlight(model) {
    var allowedIds = new Set(model.ids);
    var upstream = ancestorsOf(state.selectedId, undefined, allowedIds);
    var downstream = descendantsOf(state.selectedId, undefined, allowedIds);
    var upstreamEdges = new Set();
    var downstreamEdges = new Set();
    model.edges.forEach(function (edge) {
      if (upstream.has(edge.source) &&
          (upstream.has(edge.target) || edge.target === state.selectedId)) {
        upstreamEdges.add(edge.id);
      }
      if ((edge.source === state.selectedId || downstream.has(edge.source)) &&
          downstream.has(edge.target)) {
        downstreamEdges.add(edge.id);
      }
    });
    return {
      upstream: upstream,
      downstream: downstream,
      upstreamEdges: upstreamEdges,
      downstreamEdges: downstreamEdges
    };
  }

  function reviewerGraphNodeStyle(item, highlight) {
    var section = sectionMeta(item.section);
    if (item.id === state.selectedId) {
      return { fill: "#f7e8bf", stroke: "#a5630f", font: "#4b3210", width: 2.8 };
    }
    if (highlight.upstream.has(item.id)) {
      return { fill: "#eee8f8", stroke: "#7654a6", font: "#4a3970", width: 2.2 };
    }
    if (highlight.downstream.has(item.id)) {
      return { fill: "#fff0d6", stroke: "#b97819", font: "#744a10", width: 2.2 };
    }
    if (item.dependencyEvidence === "source-only") {
      return { fill: "#f7f9fb", stroke: "#8b96a1", font: "#66727d", width: 1.4 };
    }
    if (state.selectedId) {
      return { fill: "#f7f9fb", stroke: "#cbd4dd", font: "#8a96a1", width: 1.1 };
    }
    return {
      fill: section.wash || "#e9effa",
      stroke: section.color || "#315fb5",
      font: "#253544",
      width: 1.5
    };
  }

  function reviewerGraphEdgeStyle(edge, highlight) {
    var base = edge.kind === "statement"
      ? { color: "#7654a6", width: 1.45, dash: "7,4" }
      : edge.kind === "proof"
        ? { color: "#28768a", width: 1.55, dash: "" }
        : edge.kind === "both"
          ? { color: "#a5630f", width: 2.05, dash: "" }
          : { color: "#aab5bf", width: 1.35, dash: "" };
    if (highlight.upstreamEdges.has(edge.id) || highlight.downstreamEdges.has(edge.id)) {
      return { color: base.color, width: Math.max(2.35, base.width + 0.7), dash: base.dash, active: true };
    }
    if (state.selectedId) {
      return { color: "#cbd4dd", width: 1.1, dash: base.dash, active: false };
    }
    return { color: base.color, width: base.width, dash: base.dash, active: false };
  }

  function buildReviewerGraphDot(model, highlight) {
    var lines = [
      "digraph G {",
      '  graph [rankdir="LR", bgcolor="transparent", pad="0.25", nodesep="0.28", ranksep="0.72", outputorder="edgesfirst", splines="spline"];',
      '  node [style="rounded,filled", fontname="Segoe UI", fontsize="10", margin="0.15,0.09"];',
      '  edge [arrowhead="normal", arrowsize="0.7"];'
    ];
    model.ids.forEach(function (id) {
      var item = itemById.get(id);
      var style = reviewerGraphNodeStyle(item, highlight);
      var shape = item.type === "Theorem" || item.type === "Proposition" ? "ellipse" : "box";
      lines.push(
        '  "' + escapeReviewerDot(id) + '" ' +
        '[id="node-' + escapeReviewerDot(reviewerGraphDomId(id)) + '" ' +
        'label="' + escapeReviewerDot(item.label) + '" ' +
        'tooltip="' + escapeReviewerDot(item.label + " - " + item.title) + '" ' +
        'shape="' + shape + '" ' +
        'style="' + (item.dependencyEvidence === "source-only" ? "rounded,dashed,filled" : "rounded,filled") + '" ' +
        'fillcolor="' + style.fill + '" ' +
        'color="' + style.stroke + '" ' +
        'fontcolor="' + style.font + '" ' +
        'penwidth="' + style.width + '"];'
      );
    });
    model.edges.slice().sort(function (left, right) {
      return itemSort(left.source, right.source) || itemSort(left.target, right.target);
    }).forEach(function (edge) {
      var style = reviewerGraphEdgeStyle(edge, highlight);
      lines.push(
        '  "' + escapeReviewerDot(edge.source) + '" -> "' + escapeReviewerDot(edge.target) + '" ' +
        '[id="edge-' + escapeReviewerDot(reviewerGraphDomId(edge.id)) + '" ' +
        'color="' + style.color + '" penwidth="' + style.width + '" ' +
        (style.dash ? 'style="dashed" ' : '') +
        'tooltip="' + escapeReviewerDot((edge.kind || "legacy") + " dependency") + '"];'
      );
    });
    lines.push("}");
    return lines.join("\n");
  }

  function loadReviewerVizRuntime() {
    if (window.Viz) {
      return Promise.resolve();
    }
    if (!state.vizScriptPromise) {
      state.vizScriptPromise = new Promise(function (resolve, reject) {
        var script = document.createElement("script");
        script.src = "./vendor/viz-global.js";
        script.async = true;
        script.onload = function () { resolve(); };
        script.onerror = function () {
          state.vizScriptPromise = null;
          script.remove();
          reject(new Error("Graphviz runtime could not be loaded."));
        };
        document.head.appendChild(script);
      });
    }
    return state.vizScriptPromise;
  }

  function getReviewerGraphviz() {
    if (state.graphviz) {
      return Promise.resolve(state.graphviz);
    }
    if (!state.graphvizPromise) {
      state.graphvizPromise = loadReviewerVizRuntime()
        .then(function () { return window.Viz.instance(); })
        .then(function (viz) {
          state.graphviz = viz;
          return viz;
        })
        .catch(function (error) {
          state.graphvizPromise = null;
          throw error;
        });
    }
    return state.graphvizPromise;
  }

  function reviewerGraphSvgSize(svg) {
    var viewBox = svg.getAttribute("viewBox");
    if (viewBox) {
      var values = viewBox.trim().split(/[ ,]+/).map(Number);
      if (values.length === 4 && values.every(function (value) {
        return Number.isFinite(value);
      })) {
        return { width: values[2], height: values[3] };
      }
    }
    return {
      width: parseFloat(svg.getAttribute("width")) || 800,
      height: parseFloat(svg.getAttribute("height")) || 500
    };
  }

  function decorateReviewerGraphvizSvg(svg, model, highlight) {
    var visibleIds = new Set(model.ids);
    var edgesById = new Map();
    var edgesByDomId = new Map();
    model.edges.forEach(function (edge) {
      edgesById.set(edge.id, edge);
      edgesByDomId.set("edge-" + reviewerGraphDomId(edge.id), edge);
    });
    svg.querySelectorAll("g.node").forEach(function (node) {
      var title = node.querySelector("title");
      var id = node.dataset.nodeId || (title ? title.textContent.trim() : "");
      var item = itemById.get(id);
      if (!item) {
        return;
      }
      node.style.display = visibleIds.has(id) ? "" : "none";
      if (!visibleIds.has(id)) {
        delete node.dataset.nodeId;
        node.removeAttribute("tabindex");
        return;
      }
      node.dataset.nodeId = id;
      node.setAttribute("tabindex", "0");
      node.setAttribute("role", "button");
      node.setAttribute("aria-label", item.label + ": " + item.title);
      node.classList.add("graph-node");
      node.classList.remove("selected", "upstream", "downstream", "dim", "source-only");
      if (item.dependencyEvidence === "source-only") {
        node.classList.add("source-only");
      }
      applySectionStyle(node, item.section);
      if (id === state.selectedId) {
        node.classList.add("selected");
      } else if (highlight.upstream.has(id)) {
        node.classList.add("upstream");
      } else if (highlight.downstream.has(id)) {
        node.classList.add("downstream");
      } else if (state.selectedId) {
        node.classList.add("dim");
      }
      var style = reviewerGraphNodeStyle(item, highlight);
      var shape = node.querySelector("ellipse, polygon, path");
      if (shape) {
        shape.classList.add("node-box");
        shape.setAttribute("fill", style.fill);
        shape.setAttribute("stroke", style.stroke);
        shape.setAttribute("stroke-width", String(style.width));
      }
      node.querySelectorAll("text").forEach(function (label) {
        label.setAttribute("fill", style.font);
        label.style.pointerEvents = "none";
      });
    });
    svg.querySelectorAll("g.edge").forEach(function (edgeGroup) {
      var title = edgeGroup.querySelector("title");
      var edgeId = edgeGroup.dataset.edgeId || (title ? title.textContent.trim() : "");
      var edge = edgesById.get(edgeId) || edgesByDomId.get(edgeGroup.id || "");
      edgeGroup.style.display = edge ? "" : "none";
      if (!edge) {
        edgeGroup.classList.remove("graph-edge");
        delete edgeGroup.dataset.edgeId;
        return;
      }
      edgeGroup.dataset.edgeId = edge.id;
      edgeGroup.dataset.dependencyKind = edge.kind;
      edgeGroup.classList.remove(
        "active", "dim", "dependency-statement", "dependency-proof",
        "dependency-both", "dependency-unclassified"
      );
      edgeGroup.classList.add("graph-edge", "dependency-" + edge.kind);
      edgeGroup.style.setProperty("marker-end", "none", "important");
      var style = reviewerGraphEdgeStyle(edge, highlight);
      if (style.active) {
        edgeGroup.classList.add("active");
      } else if (state.selectedId) {
        edgeGroup.classList.add("dim");
      }
      var path = edgeGroup.querySelector("path");
      if (path) {
        path.setAttribute("fill", "none");
        path.setAttribute("stroke", style.color);
        path.setAttribute("stroke-width", String(style.width));
        if (style.dash) {
          path.setAttribute("stroke-dasharray", style.dash);
        } else {
          path.removeAttribute("stroke-dasharray");
        }
        path.style.setProperty("marker-end", "none", "important");
      }
      var arrow = edgeGroup.querySelector("polygon");
      if (arrow) {
        arrow.setAttribute("fill", style.color);
        arrow.setAttribute("stroke", style.color);
      }
    });
  }

  function graphLayoutKey(model) {
    // A relation filter can change edges while retaining exactly the same nodes.
    return JSON.stringify([model.ids, model.edges.map(function (edge) {
      return [edge.source, edge.target, edge.kind];
    })]);
  }

  function renderReviewerGraphviz(ids, model, layoutModel, options) {
    var graphKey = graphLayoutKey(layoutModel);
    var token = ++state.renderToken;
    var highlight = reviewerGraphHighlight(model);
    refs.graphEmpty.hidden = Boolean(ids.length);
    refs.graphStats.innerHTML =
      '<span class="stat-pill">' + ids.length + '/' + items.length + ' nodes</span>' +
      '<span class="stat-pill">' + model.edges.length + ' edges</span>';
    if (!ids.length) {
      refs.graphViewport.removeAttribute("aria-busy");
      refs.graphScene.replaceChildren();
      return;
    }

    var existing = refs.graphScene.querySelector("svg[data-reviewer-graphviz-key]");
    if (existing && existing.dataset.reviewerGraphvizKey === graphKey) {
      refs.graphViewport.removeAttribute("aria-busy");
      decorateReviewerGraphvizSvg(existing, model, highlight);
      if (!options || options.fit !== false) {
        window.requestAnimationFrame(fitGraph);
      } else {
        applyTransform();
      }
      return;
    }

    refs.graphViewport.setAttribute("aria-busy", "true");
    getReviewerGraphviz()
      .then(function (viz) {
        if (token !== state.renderToken || state.layoutMode !== "natural") {
          return;
        }
        var svgText = viz.renderString(buildReviewerGraphDot(layoutModel, highlight), {
          format: "svg",
          engine: "dot"
        });
        var parsed = new DOMParser().parseFromString(svgText, "image/svg+xml");
        var svg = parsed.documentElement;
        if (!svg || String(svg.nodeName).toLowerCase() !== "svg") {
          throw new Error("Graphviz returned invalid SVG.");
        }
        var size = reviewerGraphSvgSize(svg);
        svg.setAttribute("width", String(size.width));
        svg.setAttribute("height", String(size.height));
        svg.setAttribute("role", "img");
        svg.setAttribute("aria-label", "Theorem dependency graph");
        svg.setAttribute("preserveAspectRatio", "xMinYMin meet");
        svg.dataset.reviewerGraphvizKey = graphKey;
        decorateReviewerGraphvizSvg(svg, model, highlight);
        refs.graphScene.replaceChildren(svg);
        state.graphWidth = size.width;
        state.graphHeight = size.height;
        refs.graphViewport.removeAttribute("aria-busy");
        if (!options || options.fit !== false) {
          window.requestAnimationFrame(fitGraph);
        } else {
          applyTransform();
        }
      })
      .catch(function (error) {
        if (token !== state.renderToken) {
          return;
        }
        refs.graphViewport.removeAttribute("aria-busy");
        state.layoutMode = "layered";
        writePreference("layout-mode", state.layoutMode);
        window.console.warn("Graphviz layout unavailable:", error);
        renderGraph({ fit: true });
        window.dispatchEvent(new CustomEvent("reasbook-layoutchange", {
          detail: { mode: state.layoutMode, error: String(error) }
        }));
      });
  }

  function edgePath(source, target) {
    var startX = source.x + NODE_WIDTH;
    var startY = source.y + NODE_HEIGHT / 2;
    var endX = target.x;
    var endY = target.y + NODE_HEIGHT / 2;
    var control = Math.max(30, (endX - startX) * 0.48);
    return "M " + startX + " " + startY + " C " +
      (startX + control) + " " + startY + ", " +
      (endX - control) + " " + endY + ", " + endX + " " + endY;
  }

  function renderGraph(options) {
    var ids = graphVisibleIds();
    var model = graphModel(ids);
    var layoutModel = graphLayoutModel(model);
    if (state.layoutMode === "natural") {
      renderReviewerGraphviz(ids, model, layoutModel, options);
      return;
    }
    state.renderToken += 1;
    refs.graphViewport.removeAttribute("aria-busy");
    var layout = graphLayout(layoutModel);
    var allowedIds = new Set(ids);
    var upstream = ancestorsOf(state.selectedId, undefined, allowedIds);
    var downstream = descendantsOf(state.selectedId, undefined, allowedIds);
    var edgeLayer = svgElement("g", { class: "edge-layer" });
    var nodeLayer = svgElement("g", { class: "node-layer" });
    refs.graphEmpty.hidden = Boolean(ids.length);

    model.edges.forEach(function (edge) {
      var source = layout.positions.get(edge.source);
      var target = layout.positions.get(edge.target);
      if (!source || !target) {
        return;
      }
      var path = svgElement("path", {
        class: "graph-edge dependency-" + edge.kind,
        d: edgePath(source, target),
        "data-edge-id": edge.id,
        "data-dependency-kind": edge.kind
      });
      var activeUpstream = upstream.has(edge.source) &&
        (upstream.has(edge.target) || edge.target === state.selectedId);
      var activeDownstream = (edge.source === state.selectedId || downstream.has(edge.source)) &&
        downstream.has(edge.target);
      if (activeUpstream || activeDownstream) {
        path.classList.add("active");
      } else if (state.selectedId) {
        path.classList.add("dim");
      }
      edgeLayer.appendChild(path);
    });

    ids.forEach(function (id) {
      var item = itemById.get(id);
      var position = layout.positions.get(id);
      var node = svgElement("g", {
        class: "graph-node",
        transform: "translate(" + position.x + " " + position.y + ")",
        tabindex: "0",
        role: "button",
        "aria-label": item.label + ": " + item.title,
        "data-node-id": id
      });
      applySectionStyle(node, item.section);
      if (item.dependencyEvidence === "source-only") {
        node.classList.add("source-only");
      }
      if (id === state.selectedId) {
        node.classList.add("selected");
      } else if (upstream.has(id)) {
        node.classList.add("upstream");
      } else if (downstream.has(id)) {
        node.classList.add("downstream");
      } else if (state.selectedId) {
        node.classList.add("dim");
      }
      var title = svgElement("title");
      title.textContent = item.label + " - " + item.title;
      var box = svgElement("rect", {
        class: "node-box",
        width: NODE_WIDTH,
        height: NODE_HEIGHT,
        rx: "5",
        ry: "5"
      });
      var label = svgElement("text", {
        class: "node-label",
        x: NODE_WIDTH / 2,
        y: NODE_HEIGHT / 2 + 0.5
      });
      label.textContent = item.label;
      node.appendChild(title);
      node.appendChild(box);
      node.appendChild(label);
      nodeLayer.appendChild(node);
    });

    refs.graphScene.replaceChildren(edgeLayer, nodeLayer);
    state.graphWidth = layout.width;
    state.graphHeight = layout.height;
    refs.graphStats.innerHTML =
      '<span class="stat-pill">' + ids.length + '/' + items.length + ' nodes</span>' +
      '<span class="stat-pill">' + model.edges.length + ' edges</span>';
    if (!options || options.fit !== false) {
      window.requestAnimationFrame(fitGraph);
    } else {
      applyTransform();
    }
  }

  function applyTransform() {
    refs.graphScene.setAttribute(
      "transform",
      "translate(" + state.transform.x + " " + state.transform.y + ") " +
        "scale(" + state.transform.scale + ")"
    );
    var percent = Math.round(state.transform.scale * 1000) / 10 + "%";
    refs.graphZoomSlider.value = Math.round(
      Math.log(state.transform.scale / MIN_ZOOM) / Math.log(MAX_ZOOM / MIN_ZOOM) * 1000
    );
    refs.graphZoomSlider.setAttribute("aria-valuetext", percent);
    refs.graphZoomValue.textContent = percent;
  }

  function fitGraph() {
    var rect = refs.graphViewport.getBoundingClientRect();
    if (rect.width <= 0 || rect.height <= 0) {
      return;
    }
    var scale = Math.min(
      rect.width / Math.max(state.graphWidth, 1),
      rect.height / Math.max(state.graphHeight, 1),
      1.45
    );
    scale = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, scale * 0.92));
    state.transform.scale = scale;
    state.transform.x = (rect.width - state.graphWidth * scale) / 2;
    state.transform.y = (rect.height - state.graphHeight * scale) / 2;
    applyTransform();
  }

  function zoomAt(factor, clientX, clientY) {
    var rect = refs.graphViewport.getBoundingClientRect();
    var pointX = clientX == null ? rect.width / 2 : clientX - rect.left;
    var pointY = clientY == null ? rect.height / 2 : clientY - rect.top;
    var oldScale = state.transform.scale;
    var nextScale = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, oldScale * factor));
    state.transform.x = pointX - (pointX - state.transform.x) * (nextScale / oldScale);
    state.transform.y = pointY - (pointY - state.transform.y) * (nextScale / oldScale);
    state.transform.scale = nextScale;
    applyTransform();
  }

  function appendInline(parent, text) {
    String(text).split(/(`[^`]*`)/g).forEach(function (part) {
      if (part.length >= 2 && part[0] === "`" && part[part.length - 1] === "`") {
        var code = document.createElement("code");
        code.textContent = part.slice(1, -1);
        parent.appendChild(code);
      } else {
        parent.appendChild(document.createTextNode(part));
      }
    });
  }

  function renderStatement(container, item) {
    if (item.statementHtml) {
      container.innerHTML = item.statementHtml;
      return;
    }
    var statement = String(item.statement || "No natural-language statement is available.").trim();
    var lines = statement.split(/\r?\n/);
    var paragraph = [];
    var list = null;

    function flushParagraph() {
      if (!paragraph.length) {
        return;
      }
      var element = document.createElement("p");
      appendInline(element, paragraph.join(" ").trim());
      container.appendChild(element);
      paragraph = [];
    }

    lines.forEach(function (line) {
      var bullet = line.match(/^\s*[-*]\s+(.+)$/);
      if (bullet) {
        flushParagraph();
        if (!list) {
          list = document.createElement("ul");
          container.appendChild(list);
        }
        var itemElement = document.createElement("li");
        appendInline(itemElement, bullet[1]);
        list.appendChild(itemElement);
        return;
      }
      if (!line.trim()) {
        flushParagraph();
        list = null;
        return;
      }
      list = null;
      paragraph.push(line.trim());
    });
    flushParagraph();
  }

  function relationLink(item) {
    var button = document.createElement("button");
    button.type = "button";
    button.className = "relation-link";
    button.dataset.selectItem = item.id;
    applySectionStyle(button, item.section);
    var dot = document.createElement("span");
    dot.className = "relation-dot";
    var label = document.createElement("span");
    label.className = "relation-label";
    label.textContent = item.label;
    button.appendChild(dot);
    button.appendChild(label);
    return button;
  }

  function relationColumn(title, ids) {
    var column = document.createElement("div");
    column.className = "relation-column";
    var heading = document.createElement("h4");
    heading.textContent = title + " (" + ids.length + ")";
    var list = document.createElement("div");
    list.className = "relation-list";
    if (!ids.length) {
      var empty = document.createElement("div");
      empty.className = "relation-empty";
      empty.textContent = "None at literature level.";
      list.appendChild(empty);
    } else {
      ids.slice().sort(itemSort).forEach(function (id) {
        var item = itemById.get(id);
        if (item) {
          list.appendChild(relationLink(item));
        }
      });
    }
    column.appendChild(heading);
    column.appendChild(list);
    return column;
  }

  function factRow(list, term, description) {
    var dt = document.createElement("dt");
    dt.textContent = term;
    var dd = document.createElement("dd");
    dd.textContent = description;
    list.appendChild(dt);
    list.appendChild(dd);
  }

  function renderDetail() {
    var item = selectedItem();
    if (!item) {
      refs.detailContent.replaceChildren();
      return;
    }
    var header = document.createElement("header");
    header.className = "detail-header";
    var kicker = document.createElement("div");
    kicker.className = "detail-kicker";
    var kind = document.createElement("span");
    kind.className = "detail-kind";
    kind.textContent = item.type;
    var sectionTag = document.createElement("span");
    sectionTag.className = "detail-section-tag";
    sectionTag.textContent = sectionMeta(item.section).short || sectionMeta(item.section).label;
    applySectionStyle(sectionTag, item.section);
    kicker.appendChild(kind);
    kicker.appendChild(sectionTag);
    var heading = document.createElement("h2");
    heading.textContent = item.label;
    var subheading = document.createElement("p");
    subheading.className = "detail-heading";
    subheading.textContent = item.title;
    var source = document.createElement("a");
    source.className = "detail-source-link";
    source.href = sourceUrl(item);
    source.target = "_blank";
    source.rel = "noreferrer";
    var leanMark = document.createElement("span");
    leanMark.className = "lean-mark";
    leanMark.textContent = "LEAN";
    source.appendChild(leanMark);
    source.appendChild(document.createTextNode("Open source at line " + item.line));
    header.appendChild(kicker);
    header.appendChild(heading);
    header.appendChild(subheading);
    header.appendChild(source);

    var statementSection = document.createElement("section");
    statementSection.className = "detail-section";
    var statementHeading = document.createElement("h3");
    statementHeading.textContent = "Natural-language statement";
    var statement = document.createElement("article");
    statement.className = "statement";
    renderStatement(statement, item);
    statementSection.appendChild(statementHeading);
    statementSection.appendChild(statement);

    var relationSection = document.createElement("section");
    relationSection.className = "detail-section";
    var relationHeading = document.createElement("h3");
    var sourceOnly = item.dependencyEvidence === "source-only";
    relationHeading.textContent = sourceOnly
      ? "Dependency evidence unavailable"
      : "Literature-level relations";
    var relationGrid = document.createElement("div");
    relationGrid.className = "relation-grid";
    if (sourceOnly) {
      var evidenceNote = document.createElement("p");
      evidenceNote.className = "dependency-evidence-note";
      evidenceNote.textContent = "This declaration is present in the source inventory but was not imported by the compiled project root. No dependency edges are inferred from text.";
      relationGrid.appendChild(evidenceNote);
    } else {
      relationGrid.appendChild(relationColumn("Statement prerequisites", item.statementDependencies));
      relationGrid.appendChild(relationColumn("Proof/body dependencies", item.proofDependencies));
      var classified = new Set(item.statementDependencies.concat(item.proofDependencies));
      var unclassified = item.dependencies.filter(function (id) { return !classified.has(id); });
      if (unclassified.length) {
        relationGrid.appendChild(relationColumn(
          item.dependencyEvidence === "curated" ? "Curated dependencies" : "Legacy dependencies",
          unclassified
        ));
      }
      relationGrid.appendChild(relationColumn("Used directly by", consumersById.get(item.id) || []));
    }
    relationSection.appendChild(relationHeading);
    relationSection.appendChild(relationGrid);

    var leanSection = document.createElement("section");
    leanSection.className = "detail-section";
    var leanHeading = document.createElement("h3");
    leanHeading.textContent = "Lean formalization";
    var facts = document.createElement("dl");
    facts.className = "lean-facts";
    factRow(facts, "Declaration", item.declaration);
    factRow(facts, "Module", moduleName(item));
    factRow(facts, "Source", item.file + ":" + item.line);
    factRow(facts, "Version", project.branch);
    factRow(facts, "Snapshot", String(project.commit || "").slice(0, 10));
    leanSection.appendChild(leanHeading);
    leanSection.appendChild(facts);
    refs.detailContent.replaceChildren(header, statementSection, relationSection, leanSection);
    refs.detailContent.parentElement.scrollTop = 0;
  }

  function renderHeader() {
    var item = selectedItem();
    refs.currentLabel.textContent = item ? item.label : "Theorem map";
    refs.currentLabel.title = refs.currentLabel.textContent;
    refs.currentTitle.textContent = item ? item.title : project.title;
    refs.fullGraphButton.classList.toggle("active", state.graphMode === "full");
    refs.focusGraphButton.classList.toggle("active", state.graphMode === "focus");
    refs.fullGraphButton.setAttribute("aria-pressed", String(state.graphMode === "full"));
    refs.focusGraphButton.setAttribute("aria-pressed", String(state.graphMode === "focus"));
    refs.graphDepthSelect.value = String(state.graphDepth);
    refs.graphDepthSelect.disabled = state.graphMode === "full";
    refs.graphDepthSelect.title = state.graphMode === "full"
      ? "Full graph includes all matching relationships. Switch to Neighborhood to limit layers."
      : "Up to " + state.graphDepth + " dependency hops in each direction";
  }

  function selectItem(id, options) {
    if (!itemById.has(id)) {
      return;
    }
    state.selectedId = id;
    if (!options || options.updateHash !== false) {
      window.history.replaceState(null, "", "#" + encodeURIComponent(id));
    }
    renderHeader();
    renderList();
    renderDetail();
    renderGraph({ fit: state.graphMode === "focus" });
    if (options && options.mobileDetail && window.innerWidth <= 820) {
      setMobileView("detail");
    }
  }

  function setGraphMode(mode) {
    state.graphMode = mode === "focus" ? "focus" : "full";
    writePreference("graph-mode-v2", state.graphMode);
    renderHeader();
    renderGraph({ fit: true });
  }

  function setSidebarCollapsed(collapsed) {
    state.sidebarCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("sidebar-collapsed", state.sidebarCollapsed);
    refs.sidebarToggle.textContent = state.sidebarCollapsed ? ">" : "<";
    refs.sidebarToggle.setAttribute("aria-expanded", String(!state.sidebarCollapsed));
    refs.sidebarToggle.setAttribute("aria-label", state.sidebarCollapsed ? "Expand index" : "Collapse index");
    refs.sidebarToggle.title = state.sidebarCollapsed ? "Expand index" : "Collapse index";
    writePreference("sidebar-collapsed", String(state.sidebarCollapsed));
    window.setTimeout(fitGraph, 170);
  }

  function setDetailCollapsed(collapsed) {
    state.detailCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("detail-collapsed", state.detailCollapsed);
    refs.detailToggle.textContent = state.detailCollapsed ? "<" : ">";
    refs.detailToggle.setAttribute("aria-expanded", String(!state.detailCollapsed));
    refs.detailToggle.setAttribute("aria-label", state.detailCollapsed ? "Expand statement" : "Collapse statement");
    refs.detailToggle.title = state.detailCollapsed ? "Expand statement" : "Collapse statement";
    writePreference("detail-collapsed", String(state.detailCollapsed));
    window.setTimeout(fitGraph, 170);
  }

  function setMobileView(view) {
    state.mobileView = view === "detail" ? "detail" : "graph";
    refs.workspace.dataset.mobileView = state.mobileView;
    refs.mobileGraphButton.classList.toggle("active", state.mobileView === "graph");
    refs.mobileDetailButton.classList.toggle("active", state.mobileView === "detail");
    if (state.mobileView === "graph") {
      window.requestAnimationFrame(fitGraph);
    }
  }

  function bindEvents() {
    refs.sidebarToggle.addEventListener("click", function () {
      setSidebarCollapsed(!state.sidebarCollapsed);
    });
    refs.detailToggle.addEventListener("click", function () {
      setDetailCollapsed(!state.detailCollapsed);
    });
    refs.searchInput.addEventListener("input", renderList);
    refs.sectionFilter.addEventListener("change", function () {
      renderList();
      renderGraph({ fit: true });
    });
    refs.typeFilter.addEventListener("change", renderList);
    refs.itemList.addEventListener("click", function (event) {
      var row = event.target.closest("[data-item-id]");
      if (row) {
        selectItem(row.dataset.itemId, { mobileDetail: true });
      }
    });
    refs.itemList.addEventListener("keydown", function (event) {
      if (event.key !== "ArrowDown" && event.key !== "ArrowUp") {
        return;
      }
      event.preventDefault();
      if (!state.visibleListIds.length) {
        return;
      }
      var index = state.visibleListIds.indexOf(state.selectedId);
      var direction = event.key === "ArrowDown" ? 1 : -1;
      var next = (Math.max(index, 0) + direction + state.visibleListIds.length) % state.visibleListIds.length;
      selectItem(state.visibleListIds[next], { updateHash: true });
    });
    refs.fullGraphButton.addEventListener("click", function () { setGraphMode("full"); });
    refs.focusGraphButton.addEventListener("click", function () { setGraphMode("focus"); });
    refs.graphDepthSelect.addEventListener("change", function () {
      var depth = Number(refs.graphDepthSelect.value);
      state.graphDepth = [1, 2, 3, 4, 5, 8].indexOf(depth) >= 0 ? depth : 3;
      writePreference("graph-depth", String(state.graphDepth));
      renderHeader();
      renderGraph({ fit: true });
    });
    refs.zoomOutButton.addEventListener("click", function () { zoomAt(0.82); });
    refs.zoomInButton.addEventListener("click", function () { zoomAt(1.22); });
    refs.fitButton.addEventListener("click", fitGraph);
    refs.graphZoomSlider.addEventListener("input", function () {
      // Logarithmic travel keeps small zoom levels usable for large graphs.
      var scale = MIN_ZOOM * Math.pow(MAX_ZOOM / MIN_ZOOM, Number(refs.graphZoomSlider.value) / 1000);
      zoomAt(scale / state.transform.scale);
    });
    refs.mobileGraphButton.addEventListener("click", function () { setMobileView("graph"); });
    refs.mobileDetailButton.addEventListener("click", function () { setMobileView("detail"); });
    refs.dependencyGraph.addEventListener("click", function (event) {
      var node = event.target.closest("[data-node-id]");
      if (node) {
        selectItem(node.dataset.nodeId, { mobileDetail: false });
      }
    });
    refs.dependencyGraph.addEventListener("keydown", function (event) {
      var node = event.target.closest("[data-node-id]");
      if (node && (event.key === "Enter" || event.key === " ")) {
        event.preventDefault();
        selectItem(node.dataset.nodeId, { mobileDetail: false });
      }
    });
    refs.detailContent.addEventListener("click", function (event) {
      var relation = event.target.closest("[data-select-item]");
      if (relation) {
        selectItem(relation.dataset.selectItem, { mobileDetail: true });
      }
    });
    refs.graphViewport.addEventListener("wheel", function (event) {
      event.preventDefault();
      zoomAt(Math.exp(-event.deltaY * 0.0012), event.clientX, event.clientY);
    }, { passive: false });
    refs.graphViewport.addEventListener("pointerdown", function (event) {
      if (event.target.closest("[data-node-id]")) {
        return;
      }
      event.preventDefault();
      refs.graphViewport.setPointerCapture(event.pointerId);
      refs.graphViewport.classList.add("dragging");
      state.pointer = {
        id: event.pointerId,
        startX: event.clientX,
        startY: event.clientY,
        originX: state.transform.x,
        originY: state.transform.y
      };
    });
    refs.graphViewport.addEventListener("pointermove", function (event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      state.transform.x = state.pointer.originX + event.clientX - state.pointer.startX;
      state.transform.y = state.pointer.originY + event.clientY - state.pointer.startY;
      applyTransform();
    });
    function endPointer(event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      state.pointer = null;
      refs.graphViewport.classList.remove("dragging");
      if (refs.graphViewport.hasPointerCapture(event.pointerId)) {
        refs.graphViewport.releasePointerCapture(event.pointerId);
      }
    }
    refs.graphViewport.addEventListener("pointerup", endPointer);
    refs.graphViewport.addEventListener("pointercancel", endPointer);
    refs.graphViewport.addEventListener("dblclick", fitGraph);
    window.addEventListener("hashchange", function () {
      var id = decodeURIComponent(window.location.hash.replace(/^#/, ""));
      if (itemById.has(id) && id !== state.selectedId) {
        selectItem(id, { updateHash: false });
      }
    });
    var resizeTimer = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(fitGraph, 100);
    });
  }

  function validateAndLoad(payload) {
    if (!payload || (payload.schemaVersion !== 1 && payload.schemaVersion !== 2) ||
        !payload.project || !Array.isArray(payload.items)) {
      throw new Error("data.json does not match theorem-map schema version 1 or 2.");
    }
    data = payload;
    project = data.project;
    preferencePrefix += ":" + String(project.id || "project");
    items = data.items.map(function (item) {
      var statementDependencies = Array.isArray(item.statementDependencies)
        ? item.statementDependencies.slice() : [];
      var proofDependencies = Array.isArray(item.proofDependencies)
        ? item.proofDependencies.slice() : [];
      var dependencies = Array.isArray(item.dependencies)
        ? item.dependencies.slice()
        : statementDependencies.concat(proofDependencies).filter(function (id, index, values) {
          return values.indexOf(id) === index;
        });
      return Object.assign({}, item, {
        statementDependencies: statementDependencies,
        proofDependencies: proofDependencies,
        dependencies: dependencies,
        dependencyEvidence: item.dependencyEvidence === "source-only" ||
          (!item.dependencyEvidence && data.generation && data.generation.mode === "source-fallback")
          ? "source-only" : item.dependencyEvidence === "curated" ? "curated" : "compiled"
      });
    });
    sections = Array.isArray(data.sections) ? data.sections.slice() : [];
    if (!sections.length) {
      Array.from(new Set(items.map(function (item) { return item.section || "overview"; })))
        .forEach(function (id, index) {
          var palette = [
            ["#315fb5", "#e9effa"], ["#23745d", "#e4f2ed"],
            ["#a14d3d", "#f8eae6"], ["#9a6a12", "#fbf1d8"]
          ][index % 4];
          sections.push({ id: id, label: id, short: id, color: palette[0], wash: palette[1] });
        });
    }
    sections.forEach(function (section) { sectionById.set(section.id, section); });
    items.forEach(function (item, index) {
      item.section = item.section || (sections[0] && sections[0].id) || "overview";
      itemById.set(item.id, item);
      orderById.set(item.id, index);
      consumersById.set(item.id, []);
    });
    items.forEach(function (item) {
      item.dependencies = item.dependencies.filter(function (dependency) {
        return itemById.has(dependency) && dependency !== item.id;
      });
      item.statementDependencies = item.statementDependencies.filter(function (dependency) {
        return itemById.has(dependency) && dependency !== item.id;
      });
      item.proofDependencies = item.proofDependencies.filter(function (dependency) {
        return itemById.has(dependency) && dependency !== item.id;
      });
      item.dependencies.forEach(function (dependency) {
        consumersById.get(dependency).push(item.id);
      });
    });
  }

  function initialize() {
    document.title = project.title + " - Theorem Map";
    refs.projectName.textContent = project.title;
    refs.brandMark.textContent = String(project.id || "RB")
      .split(/[_\s-]+/)
      .filter(Boolean)
      .slice(0, 2)
      .map(function (part) { return part[0].toUpperCase(); })
      .join("") || "RB";
    populateFilters();
    renderLegend();
    var hashId = decodeURIComponent(window.location.hash.replace(/^#/, ""));
    state.selectedId = itemById.has(hashId) ? hashId : (items[0] ? items[0].id : "");
    var savedLayout = readPreference("layout-mode");
    state.layoutMode = savedLayout === "layered" ? "layered" : "natural";
    window.dispatchEvent(new CustomEvent("reasbook-layoutchange", {
      detail: { mode: state.layoutMode }
    }));
    // v1 defaulted to full and persisted it automatically. Do not migrate that
    // incidental value into the bounded default; explicit v2 choices persist.
    var savedMode = readPreference("graph-mode-v2");
    state.graphMode = savedMode === "full" ? "full" : "focus";
    var savedDepth = Number(readPreference("graph-depth"));
    state.graphDepth = [1, 2, 3, 4, 5, 8].indexOf(savedDepth) >= 0 ? savedDepth : 3;
    state.sidebarCollapsed = readPreference("sidebar-collapsed") === "true";
    state.detailCollapsed = readPreference("detail-collapsed") === "true";
    setSidebarCollapsed(state.sidebarCollapsed);
    setDetailCollapsed(state.detailCollapsed);
    setMobileView("graph");
    bindEvents();
    renderHeader();
    renderList();
    renderDetail();
    renderGraph({ fit: true });
  }

  window.__reasbookTheoremMapLayout = {
    getMode: function () {
      return state.layoutMode;
    },
    setMode: function (mode) {
      state.layoutMode = mode === "natural" ? "natural" : "layered";
      writePreference("layout-mode", state.layoutMode);
      if (data) {
        renderGraph({ fit: true });
      }
      window.dispatchEvent(new CustomEvent("reasbook-layoutchange", {
        detail: { mode: state.layoutMode }
      }));
    }
  };

  window.__reasbookTheoremMapDependencies = {
    getMode: function () { return state.dependencyMode; },
    setMode: function (mode) {
      var next = ["statement", "proof", "statement-edges"].indexOf(mode) >= 0 ? mode : "all";
      if (next === state.dependencyMode) return;
      var sharedLayout = ["proof", "statement-edges"];
      var preserveCamera = sharedLayout.indexOf(next) >= 0 && sharedLayout.indexOf(state.dependencyMode) >= 0;
      state.dependencyMode = next;
      if (data) renderGraph({ fit: !preserveCamera });
    }
  };

  fetch("./data.json", { cache: "no-cache" })
    .then(function (response) {
      if (!response.ok) {
        throw new Error("Could not load data.json (HTTP " + response.status + ").");
      }
      return response.json();
    })
    .then(function (payload) {
      validateAndLoad(payload);
      initialize();
    })
    .catch(function (error) {
      refs.fatalError.hidden = false;
      refs.fatalError.textContent = "The theorem map could not start.\n\n" + error.message;
    });
}());
