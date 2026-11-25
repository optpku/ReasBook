#!/usr/bin/env python3
"""Render the revised paper map from a source-bound compiled SDK export.

The reviewed paper-to-Lean mapping lives in theorem-map/paper-results.json.
Dependency edges are derived only from compiled expression references. Every
edge retains a concrete declaration path, and pending worktree snapshots never
claim to be available at an upstream immutable commit.
"""

from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from typing import Any

from theorem_graph_sdk.analysis import PALETTE, contract_dependencies
from theorem_graph_sdk.generator import RESOURCE_ROOT
from theorem_graph_sdk.render import copy_generic_map


PROJECT_ID = "glowinski_admm_counterexample"
TITLE = "The multiplier step size in classical two-block ADMM: convergence and counterexamples"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes(root: Path) -> dict[str, str]:
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob("*.lean"))}


def snapshot(hashes: dict[str, str]) -> str:
    return hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()


def export_compiled(root: Path, raw: Path, provenance: Path, lake: str, extractor: Path) -> None:
    """Invoke the SDK extractor only after the root has compiled; record its snapshot."""
    import resource

    assert not raw.exists() and not provenance.exists(), "Use fresh export paths"
    hashes = source_hashes(root)
    raw.parent.mkdir(parents=True, exist_ok=True)
    config = raw.with_suffix(".config.json")
    config.write_text(json.dumps({"projects": [{"id": PROJECT_ID,
        "rootModule": PROJECT_ID + ".Paper", "rootModules": []}]}, indent=2) + "\n")
    lake_path = Path(shutil.which(lake) or lake).resolve()
    assert lake_path.is_file() and extractor.is_file()
    command = [str(lake_path), "env", "lean", "-j1", "-M4096", "-s65520", "--run",
               str(extractor.resolve()), str(config.resolve()), str(raw.resolve())]
    env = dict(os.environ)
    env["PATH"] = str(lake_path.parent) + os.pathsep + env.get("PATH", "")
    env["LAKE_NO_CACHE"] = "true"
    started = time.monotonic()
    # The SDK's JSON pretty-printer needs a larger stack for this environment.
    limits = resource.getrlimit(resource.RLIMIT_STACK)
    soft, hard = limits
    target_stack = 65520 * 1024
    if hard != resource.RLIM_INFINITY:
        target_stack = min(target_stack, hard)
    if soft != resource.RLIM_INFINITY and soft < target_stack:
        resource.setrlimit(resource.RLIMIT_STACK, (target_stack, hard))
    try:
        with raw.with_suffix(".log").open("w") as log:
            result = subprocess.run(command, cwd=root.parents[1], env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
    finally:
        resource.setrlimit(resource.RLIMIT_STACK, limits)
    assert result.returncode == 0, f"SDK compiled export failed; see {raw.with_suffix('.log')}"
    assert hashes == source_hashes(root), "Sources changed during extraction"
    provenance.parent.mkdir(parents=True, exist_ok=True)
    provenance.write_text(json.dumps({
        "status": "passed_compiled_export", "is_lean_proof_check": False,
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": time.monotonic() - started, "command": command,
        "extractor_sha256": sha(extractor), "source_files_sha256": hashes,
        "source_snapshot_sha256": snapshot(hashes), "raw_sha256": sha(raw),
    }, indent=2) + "\n")


def edge_paths(members: list[str], raw: dict[str, dict[str, Any]],
               owners: dict[str, str], node_id: str, field: str) -> dict[str, list[str]]:
    """Keep a shortest actual constant-reference path for each contracted edge."""
    queue = deque((dep, [member, dep]) for member in members
                  for dep in sorted(raw[member][field]))
    visited: set[str] = set()
    found: dict[str, list[str]] = {}
    while queue:
        name, path = queue.popleft()
        if name in visited:
            continue
        visited.add(name)
        if name in owners:
            if owners[name] != node_id:
                found.setdefault(owners[name], path)
            continue
        # Origin class is retained from the first edge. Helpers use their union,
        # as in the SDK, so traversing a definition body does not lose evidence.
        queue.extend((dep, path + [dep]) for dep in sorted(raw[name]["dependencies"]))
    return found


def customize_frontend(output: Path) -> None:
    """Expose all mapped proof components and respect pending source identity."""
    app = output / "app.js"
    source = app.read_text()
    marker = '  function sourceUrl(item) {\n'
    assert source.count(marker) == 1
    source = source.replace(marker, marker + '''    if (project.publicationPending) {
      return String(project.localSourceRoot || "../") + encodePath(item.file || "") +
        "#L" + Number(item.line || 1);
    }
''', 1)
    source = source.replace('"Open source at line " + item.line',
                            '(project.publicationPending ? "Open local source at line " : "Open source at line ") + item.line')
    marker = '    leanSection.appendChild(facts);\n'
    assert source.count(marker) == 1
    source = source.replace(marker, marker + '''    if (item.correspondence) {
      var scope = document.createElement("p");
      scope.className = "mapping-correspondence";
      scope.textContent = item.correspondence;
      leanSection.appendChild(scope);
    }
    var bindings = document.createElement("ul");
    bindings.className = "mapped-declarations";
    (item.declarationBindings || []).forEach(function (binding) {
      var row = document.createElement("li");
      var link = document.createElement("a");
      link.href = sourceUrl(binding);
      link.target = "_blank";
      link.rel = "noreferrer";
      var code = document.createElement("code");
      code.textContent = binding.name;
      link.appendChild(code);
      row.appendChild(link);
      row.appendChild(document.createTextNode(" — " + binding.file + ":" + binding.line));
      bindings.appendChild(row);
    });
    leanSection.appendChild(bindings);
    if (project.publicationPending) {
      var pending = document.createElement("p");
      pending.className = "dependency-evidence-note";
      pending.textContent = "Verified local source snapshot; publication and immutable source links are pending the source merge and maintainer release.";
      leanSection.appendChild(pending);
    }
''', 1)
    # The release context is the SDK's authoritative identity for curated maps.
    # This avoids using the preparation worktree's identity after publication.
    marker = '''    .then(function (payload) {
      validateAndLoad(payload);
      initialize();
    })'''
    assert source.count(marker) == 1
    source = source.replace(marker, '''    .then(function (payload) {
      return fetch("./release-context.json", { cache: "no-cache" })
        .then(function (response) { return response.ok ? response.json() : null; })
        .catch(function () { return null; })
        .then(function (context) {
          var identity = context && context.project;
          if (identity && identity.id === payload.project.id &&
              identity.sourceRoot === payload.project.sourceRoot &&
              /^[0-9a-f]{40}$/i.test(String(identity.commit || ""))) {
            payload.project = Object.assign({}, payload.project, identity, { publicationPending: false });
          }
          validateAndLoad(payload);
          initialize();
        });
    })''', 1)
    app.write_text(source)
    css = output / "styles.css"
    css.write_text(css.read_text() + '''\n/* The complete, reviewed paper-to-Lean correspondence. */
.mapped-declarations { padding-left: 1.25rem; }
.mapped-declarations li { margin: .65rem 0; overflow-wrap: anywhere; }
.mapping-correspondence { line-height: 1.6; }

/* Keep the numbered paper's full-graph action accessible on small screens. */
@media (max-width: 820px) {
  .toolbar { flex-direction: column; align-items: stretch; gap: 8px; }
  .toolbar-title { max-width: 100%; }
  .toolbar-actions { flex-wrap: wrap; overflow: visible; }
  .toolbar-actions .segmented { display: inline-flex; }
  .graph-scope-heading { flex: 1 1 100%; min-width: 0; justify-content: space-between; }
  .graph-selection-label { min-width: 0; white-space: normal; font-size: 13px; }
}
''')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path)
    parser.add_argument("--mapping", type=Path)
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--provenance", type=Path, required=True)
    parser.add_argument("--export", action="store_true", help="Run the SDK extractor against the compiled Paper root first")
    parser.add_argument("--lake", default="lake", help="Branch-pinned Lake executable for --export")
    parser.add_argument("--extractor", type=Path, default=RESOURCE_ROOT / "Extract.lean")
    parser.add_argument("--commit", help="Immutable source commit, after the contribution is committed or merged")
    parser.add_argument("--local-source-root", default="../")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = (args.project_root or Path(__file__).resolve().parents[1]).resolve()
    if args.export:
        export_compiled(root, args.raw, args.provenance, args.lake, args.extractor)
    mapping_path = args.mapping or root / "theorem-map/paper-results.json"
    mapping = json.loads(mapping_path.read_text())
    assert len(mapping) == 14 and len({item["id"] for item in mapping}) == 14
    assert len([item for item in mapping if item["type"] != "Certificate"]) == 12
    provenance = json.loads(args.provenance.read_text())
    hashes = source_hashes(root)
    snap = snapshot(hashes)
    assert provenance["status"] == "passed_compiled_export"
    assert provenance["raw_sha256"] == sha(args.raw)
    assert provenance["source_files_sha256"] == hashes
    assert provenance["source_snapshot_sha256"] == snap
    exported = json.loads(args.raw.read_text())
    assert len(exported) == 1 and exported[0]["id"] == PROJECT_ID
    assert exported[0]["rootModule"] == PROJECT_ID + ".Paper"
    raw = {item["name"]: item for item in exported[0]["declarations"]}
    assert len(raw) == len(exported[0]["declarations"]) > 0
    for name, item in raw.items():
        assert all(isinstance(item[field], list) for field in
                   ("dependencies", "statementDependencies", "proofDependencies")), name
        assert set(item["dependencies"]) == set(item["statementDependencies"]) | set(item["proofDependencies"]), name
        assert all(dep in raw for dep in item["dependencies"]), name
    owners: dict[str, str] = {}
    for item in mapping:
        assert item["declarations"]
        for name in item["declarations"]:
            assert name in raw and raw[name]["kind"] == "theorem", name
            assert name not in owners, f"Ambiguous manuscript ownership: {name}"
            owners[name] = item["id"]

    commit = "uncommitted-" + snap
    if args.commit:
        assert re.fullmatch(r"[0-9a-f]{40}", args.commit), "Use a full immutable source commit"
        repo = root.parents[2]
        prefix = root.relative_to(repo).as_posix()
        expected = sorted(prefix + "/" + name for name in hashes)
        committed = subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", args.commit, "--", prefix], cwd=repo, text=True)
        assert sorted(name for name in committed.splitlines() if name.endswith(".lean")) == expected
        subprocess.run(["git", "diff", "--quiet", args.commit, "--",
                        f":(glob){prefix}/**/*.lean", f"{prefix}/*.lean"], cwd=repo, check=True)
        commit = args.commit

    nodes, witnesses = [], []
    for specification in mapping:
        node = dict(specification)
        members = node.pop("declarations")
        primary = raw[members[0]]
        bindings = []
        for name in members:
            declaration = raw[name]
            module = declaration["moduleName"]
            assert module.startswith(PROJECT_ID + "."), module
            file = module.removeprefix(PROJECT_ID + ".").replace(".", "/") + ".lean"
            assert file in hashes, file
            bindings.append({"name": name, "file": file, "line": declaration["line"],
                             "module": module, "kind": declaration["kind"],
                             "sourceSha256": hashes[file]})
        node.update(declaration=members[0], file=bindings[0]["file"], line=primary["line"],
                    module=primary["moduleName"], interfaceDeclarations=members,
                    declarationBindings=bindings, dependencyEvidence="compiled")
        for field in ("statementDependencies", "proofDependencies"):
            contracted = sorted({dependency for member in members for dependency in
                                 contract_dependencies(member, raw, owners, field)} - {node["id"]})
            paths = edge_paths(members, raw, owners, node["id"], field)
            assert contracted == sorted(paths), (node["id"], field)
            node[field] = contracted
            for destination, path in sorted(paths.items()):
                assert path[1] in raw[path[0]][field]
                assert all(b in raw[a]["dependencies"] for a, b in zip(path[1:], path[2:]))
                witnesses.append({"from": node["id"], "to": destination,
                                  "kind": "statement" if field.startswith("statement") else "proof",
                                  "declarationPath": path})
        node["dependencies"] = sorted(set(node["statementDependencies"] + node["proofDependencies"]))
        nodes.append(node)
    sections = []
    for section in dict.fromkeys(node["section"] for node in nodes):
        color, wash = PALETTE[len(sections) % len(PALETTE)]
        number = section.removeprefix("section-")
        label = "Appendix C" if number == "C" else "Section " + number
        sections.append({"id": section, "label": label, "short": label, "color": color, "wash": wash})
    data = {
        "schemaVersion": 2,
        "project": {"id": PROJECT_ID, "title": TITLE, "kind": "papers", "branch": "v4.32.0",
                    "commit": commit, "repository": "https://github.com/optpku/ReasBook",
                    "sourceRoot": "ReasBook/Papers/" + PROJECT_ID + "/",
                    "sourceSnapshotSha256": snap, "publicationPending": not bool(args.commit),
                    "localSourceRoot": args.local_source_root,
                    "paper": "https://arxiv.org/abs/2611.09169"},
        "sections": sections, "items": nodes,
        "generation": {"mode": "lean-environment", "sourceFallback": False,
                       "dependencyCoverage": "complete for all mapped proof components",
                       "dependencyModel": "compiled-paper-component-contraction-v2",
                       "rootModule": exported[0]["rootModule"], "rawDeclarationCount": len(raw),
                       "rawSha256": sha(args.raw), "sourceOnlyItemCount": 0,
                       "compiledItemCount": len(nodes), "numberedResultCount": 12,
                       "unnumberedCertificateCount": 2, "mappedTheoremCount": len(owners),
                       "edgeWitnesses": "edge-witnesses.json",
                       "correspondence": "Reviewed explicit mapping to the revised manuscript; edges come only from compiled Lean expressions."},
    }
    copy_generic_map(RESOURCE_ROOT / "assets", args.output, data)
    customize_frontend(args.output)
    if mapping_path.resolve() != (args.output / "paper-results.json").resolve():
        shutil.copy2(mapping_path, args.output / "paper-results.json")
    (args.output / "source-manifest.json").write_text(json.dumps(
        {"sourceSnapshotSha256": snap, "files_sha256": hashes}, indent=2) + "\n")
    (args.output / "edge-witnesses.json").write_text(json.dumps(
        {"rawSha256": sha(args.raw), "sourceSnapshotSha256": snap, "edges": witnesses}, indent=2) + "\n")
    print(json.dumps({"nodes": len(nodes), "edges": sum(len(n["dependencies"]) for n in nodes),
                      "mapped_theorems": len(owners), "publication_pending": not bool(args.commit),
                      "source_snapshot_sha256": snap}, indent=2))


if __name__ == "__main__":
    main()
