// Run with node sdk/theorem_graph/tests/test_graph_view.js; no browser or npm dependencies.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

const source = fs.readFileSync(path.join(__dirname, "../src/theorem_graph_sdk/resources/assets/app.js"), "utf8");
const elements = new Map();
const context = {
  document: { getElementById: (id) => {
    if (!elements.has(id)) elements.set(id, {
      value: "all", attributes: {},
      setAttribute(name, value) { this.attributes[name] = value; },
      getBoundingClientRect: () => ({ left: 0, top: 0, width: 800, height: 600 }),
    });
    return elements.get(id);
  } },
  window: {},
  fetch: () => new Promise(() => {}),
};
vm.runInNewContext(source.replace('  fetch("./data.json"', `
  window.testGraph = {
    set: function (input, selected, mode, depth, dependencyMode) {
      items = input;
      itemById = new Map(input.map(function (item) { return [item.id, item]; }));
      orderById = new Map(input.map(function (item, index) { return [item.id, index]; }));
      consumersById = new Map();
      input.forEach(function (item) {
        item.dependencies.forEach(function (dependency) {
          if (!consumersById.has(dependency)) consumersById.set(dependency, []);
          consumersById.get(dependency).push(item.id);
        });
      });
      state.selectedId = selected;
      state.graphMode = mode;
      state.graphDepth = depth;
      state.dependencyMode = dependencyMode || "all";
    },
    visible: graphVisibleIds,
    model: graphModel,
    layoutKey: graphLayoutKey,
    layoutModel: graphLayoutModel,
    layout: graphLayout,
    highlight: reviewerGraphHighlight,
    zoom: zoomAt,
    displayMathTitle: displayMathTitle,
    displayItemLabel: displayItemLabel,
    displayItemTitle: displayItemTitle,
    fit: fitGraph,
    transform: function () { return state.transform; }
  };
  fetch("./data.json"`), context);
const api = context.window.testGraph;
assert.equal(api.displayMathTitle('Extension to every dimension $n\\ge2$'), 'Extension to every dimension n≥2');
assert.equal(api.displayMathTitle('Points lie on $\\Gamma$ and $\\mathcal E$ is closed'), 'Points lie on Γ and 𝓔 is closed');
assert.equal(api.displayMathTitle('Retain $\\unknown{x}$'), 'Retain $\\unknown{x}$');
const namedProposition = {label: 'Proposition prop:finite', title: 'Proposition prop:finite', type: 'Proposition', file: 'GlowinskiADMM/finite_objectives_and_growth.lean'};
assert.equal(api.displayItemLabel(namedProposition), 'Proposition');
assert.equal(api.displayItemTitle(namedProposition), 'Finite objectives and growth');
const item = (id, dependencies = []) => ({ id, dependencies, statementDependencies: [], proofDependencies: dependencies });
const chain = Array.from({ length: 3000 }, (_, index) => item(String(index), index ? [String(index - 1)] : []));
api.set(chain, "1500", "focus", 3);
assert.deepEqual(Array.from(api.visible()), ["1497", "1498", "1499", "1500", "1501", "1502", "1503"]);
const model = api.model(api.visible());
assert.equal(model.edges.length, 6);
assert.equal(api.highlight(model).upstream.size, 3);
assert.equal(api.highlight(model).downstream.size, 3);
api.set(chain, "1500", "focus", 1);
assert.equal(api.visible().length, 3);
api.set(chain, "1500", "full", 3);
assert.equal(api.visible().length, 3000);

// The sibling shares a prerequisite but is not a directional dependency.
// A cycle must neither include the selection twice nor loop indefinitely.
const branches = [item("root"), item("middle", ["root"]), item("selected", ["middle"]),
  item("child", ["selected"]), item("sibling", ["middle"]), item("cycle-a", ["cycle-b"]),
  item("cycle-b", ["cycle-a"]), item("unrelated")];
api.set(branches, "selected", "focus", 3);
assert.deepEqual(Array.from(api.visible()), ["root", "middle", "selected", "child"]);
api.set(branches, "cycle-a", "focus", 3);
assert.deepEqual(Array.from(api.visible()), ["cycle-a", "cycle-b"]);
api.set(branches, "unrelated", "focus", 3);
assert.deepEqual(Array.from(api.visible()), ["unrelated"]);
const mixed = [item("s2"), item("s1", ["s2"]), item("selected", ["s1", "p1"]),
  item("p1", ["p2"]), item("p2"), item("stmt-child", ["selected"]),
  item("proof-child", ["selected"]), item("unknown", ["selected"]), item("isolated")];
mixed.forEach(row => { row.proofDependencies = []; });
mixed[1].statementDependencies = ["s2"];
mixed[2].statementDependencies = ["s1"]; mixed[2].proofDependencies = ["p1"];
mixed[3].proofDependencies = ["p2"];
mixed[5].statementDependencies = ["selected"];
mixed[6].proofDependencies = ["selected"];
api.set(mixed, "selected", "focus", 1, "statement");
assert.deepEqual(Array.from(api.visible()), ["s1", "selected", "stmt-child"]);
api.set(mixed, "selected", "focus", 2, "statement");
assert.deepEqual(Array.from(api.visible()), ["s2", "s1", "selected", "stmt-child"]);
assert.equal(api.model(api.visible()).edges.length, 3);
api.set(mixed, "selected", "focus", 2, "proof");
assert.deepEqual(Array.from(api.visible()), ["selected", "p1", "p2", "proof-child"]);
assert.equal(api.model(api.visible()).edges.length, 3);
api.set(mixed, "selected", "full", 1, "proof");
assert.deepEqual(Array.from(api.visible()), ["selected", "p1", "p2", "proof-child"]);
api.set(mixed, "isolated", "focus", 3, "statement");
assert.deepEqual(Array.from(api.visible()), ["isolated"]);
api.set(mixed, "selected", "focus", 1, "statement-edges");
assert.deepEqual(Array.from(api.visible()), ["s1", "selected", "p1", "stmt-child", "proof-child"]);
assert.equal(api.model(api.visible()).edges.length, 2);
api.set(mixed, "selected", "focus", 2, "statement-edges");
assert.deepEqual(Array.from(api.visible()), ["s2", "s1", "selected", "p1", "p2", "stmt-child", "proof-child"]);
assert.equal(api.model(api.visible()).edges.length, 3);
assert.ok(api.model(api.visible()).edges.every(edge => edge.kind === "statement" || edge.kind === "both"));
api.set(mixed, "selected", "full", 1, "statement-edges");
assert.deepEqual(Array.from(api.visible()), ["s2", "s1", "selected", "p1", "p2", "stmt-child", "proof-child"]);
const sameNodes = [item("a"), item("b", ["a"]), item("c", ["a", "b"])];
sameNodes[2].statementDependencies = ["a"];
sameNodes[2].proofDependencies = ["b"];
api.set(sameNodes, "b", "focus", 3, "all");
const allModel = api.model(api.visible());
api.set(sameNodes, "b", "focus", 3, "proof");
const proofModel = api.model(api.visible());
assert.deepEqual(Array.from(allModel.ids), Array.from(proofModel.ids));
assert.equal(allModel.edges.length, 3);
assert.equal(proofModel.edges.length, 2);
assert.notEqual(api.layoutKey(allModel), api.layoutKey(proofModel));
// Shared geometry is independent of filter order, even with statement-only nodes.
for (const scope of ["focus", "full"]) {
  for (const depth of [1, 2, 3]) {
    api.set(mixed, "selected", scope, depth, "proof");
    const proofLayout = api.layoutModel(api.model(api.visible()));
    const proofPositions = api.layout(proofLayout);
    api.set(mixed, "selected", scope, depth, "statement-edges");
    const stmtLayout = api.layoutModel(api.model(api.visible()));
    assert.equal(api.layoutKey(proofLayout), api.layoutKey(stmtLayout));
    assert.deepEqual(Array.from(proofPositions.positions), Array.from(api.layout(stmtLayout).positions));
    assert.ok(api.model(api.visible()).edges.every(edge => edge.kind !== "proof"));
  }
}
assert.ok(!source.includes("-hop neighborhood"));
// Every camera operation updates the bottom control, without altering graph data.
api.zoom(1.22);
assert.equal(elements.get("graphZoomValue").textContent, "122%");
api.zoom(10000);
assert.equal(api.transform().scale, 5);
assert.equal(elements.get("graphZoomSlider").value, 1000);
api.zoom(0.00001);
assert.equal(api.transform().scale, 0.035);
assert.equal(elements.get("graphZoomSlider").value, 0);
assert.equal(elements.get("graphZoomSlider").attributes["aria-valuetext"], "3.5%");
api.fit();
assert.equal(elements.get("graphZoomValue").textContent, "133.4%");
const before = { ...api.transform() };
api.zoom(0.5);
const after = api.transform();
assert.ok(Math.abs((400 - before.x) / before.scale - (400 - after.x) / after.scale) < 1e-9);
assert.ok(Math.abs((300 - before.y) / before.scale - (300 - after.y) / after.scale) < 1e-9);
assert.equal(elements.get("graphZoomValue").textContent, "66.7%");
console.log("Graph view: typed nodes/edges/depth, full graph, cycles and isolated anchor passed.");
console.log("Graph zoom: slider synchronization, limits and centered zoom passed.");
