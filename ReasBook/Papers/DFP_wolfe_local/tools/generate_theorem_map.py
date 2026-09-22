#!/usr/bin/env python3
"""Generate the DFP theorem map using ReasBook's theorem_graph SDK.

The adapter retains the project's DFPWolfe/ReasLib module names and selects
source-declared theorems rather than assuming numbered textbook docstrings.
All edges come from compiled Lean expressions through the SDK contractor.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


MAIN_RESULTS = {
    "DFP.existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two":
        "Strong Wolfe counterexample with sharp Hölder regularity",
    "DFP.existsMatrixIdentityLiminfStrongWolfeHolder":
        "Identity initialization with Hölder regularity",
    "DFP.main_planarWeakWolfeConvergence": "Planar convergence: weak Wolfe",
    "DFP.main_planarStrongWolfeConvergence": "Planar convergence: strong Wolfe",
    "DFP.SecantIteration.planarDegeneration": "General secant degeneration",
    "DFP.main_not_globalWeakWolfeConvergence_of_parameterRange":
        "Failure of global weak-Wolfe convergence",
    "DFP.main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange":
        "Failure of level-set global weak-Wolfe convergence",
    "DFP.existsStrongWolfeCounterexample_of_parameterRange":
        "Strong Wolfe counterexample in every dimension",
    "DFP.existsMatrixIdentityLiminfStrongWolfe_of_parameterRange":
        "Identity-initialized strong Wolfe counterexample",
}


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout.strip()


def mask_comments(text: str) -> str:
    """Preserve source lines while hiding nested Lean comments and strings."""
    result = list(text)
    depth, index = 0, 0
    in_string = False
    while index < len(text):
        pair = text[index:index + 2]
        if not depth and not in_string and pair == "--":
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            result[index:end] = " " * (end - index)
            index = end
            continue
        if not in_string and pair == "/-":
            depth += 1
            result[index:index + 2] = "  "
            index += 2
            continue
        if depth and pair == "-/":
            depth -= 1
            result[index:index + 2] = "  "
            index += 2
            continue
        if not depth and text[index] == '"':
            in_string = not in_string
            result[index] = " "
        elif in_string and text[index] == "\\":
            result[index:index + 2] = "  "
            index += 2
            continue
        elif (depth or in_string) and text[index] != "\n":
            result[index] = " "
        index += 1
    return "".join(result)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk-root", type=Path, required=True,
                        help="Path to ReasBook/sdk/theorem_graph")
    parser.add_argument("--output", type=Path, required=True,
                        help="A new output directory; existing outputs are never overwritten")
    parser.add_argument("--evidence", type=Path, required=True,
                        help="A new evidence directory outside the source tree")
    parser.add_argument("--reuse-evidence", type=Path,
                        help="Reuse raw compiled evidence with matching source/extractor hashes")
    args = parser.parse_args()
    project_root = Path(__file__).resolve().parents[1]
    repo_root = project_root.parents[2]
    sdk = args.sdk_root.resolve()
    output, evidence = args.output.resolve(), args.evidence.resolve()
    if output.exists() or evidence.exists():
        parser.error("output and evidence directories must not already exist")
    if project_root in evidence.parents:
        parser.error("keep extraction evidence outside the paper source tree")
    sys.path[:0] = [str(sdk / "src"), str(sdk.parent / "common" / "src")]
    from theorem_graph_sdk.analysis import DECL_RE, PALETTE, contract_dependencies, project_title
    from theorem_graph_sdk.extractor import LeanEnvironmentExtractor
    from theorem_graph_sdk.models import Project
    from theorem_graph_sdk.render import copy_generic_map

    commit = run(["git", "rev-parse", "HEAD"], repo_root)
    source_root = "ReasBook/Papers/DFP_wolfe_local"
    tracked = run(["git", "ls-files", source_root], repo_root).splitlines()
    lean_files = [name for name in tracked if name.endswith(".lean")]
    diff = run(["git", "diff", "HEAD", "--", *lean_files], repo_root)
    if diff:
        raise RuntimeError("Lean sources differ from the recorded commit")
    source_hash = hashlib.sha256()
    for name in lean_files:
        source_hash.update(name.encode() + b"\0" + (repo_root / name).read_bytes())
    project = Project("papers", "Papers", "Paper", "DFP_wolfe_local",
                      project_root, "DFP_wolfe_local.Paper")
    resource = sdk / "src/theorem_graph_sdk/resources/Extract.lean"
    original = resource.read_text()
    old = 'moduleName.toString.splitOn "." |>.contains projectId'
    new = ('moduleName.toString.splitOn "." |>.any fun part =>\n'
           '    part == projectId || part == "DFPWolfe" || part == "ReasLib"')
    if original.count(old) != 1:
        raise RuntimeError("SDK extractor ownership predicate changed; review the adapter")
    evidence.mkdir(parents=True)
    resources = sdk / "src/theorem_graph_sdk/resources"
    sdk_hash = hashlib.sha256()
    for path in sorted((sdk / "src").rglob("*")):
        if path.is_file() and "__pycache__" not in path.parts:
            sdk_hash.update(str(path.relative_to(sdk)).encode() + b"\0" + path.read_bytes())

    def limited_runner(command, **kwargs):
        command = list(command)
        # Lean 4.32.0's derived decoder needs the optional array explicitly.
        config_path = Path(command[-2])
        config = json.loads(config_path.read_text())
        for spec in config["projects"]:
            spec.setdefault("rootModules", [])
        config_path.write_text(json.dumps(config))
        command[command.index("lean") + 1:command.index("lean") + 1] = ["-j1", "-M8192"]
        result = subprocess.run(command, **kwargs)
        (evidence / "extraction.log").write_text(result.stdout + result.stderr)
        return result

    provenance = dict(commit=commit, sourceSha256=source_hash.hexdigest(),
                      extractorSha256=hashlib.sha256(original.encode()).hexdigest())
    if args.reuse_evidence:
        saved = json.loads((args.reuse_evidence / "provenance.json").read_text())
        raw_bytes = (args.reuse_evidence / "raw.json").read_bytes()
        if any(saved.get(k) != v for k, v in provenance.items()):
            raise RuntimeError("Cached evidence does not match the source/extractor identity")
        if saved.get("rawSha256") != hashlib.sha256(raw_bytes).hexdigest():
            raise RuntimeError("Cached raw evidence checksum mismatch")
        raw = json.loads(raw_bytes)
    else:
        print("Extracting the compiled DFP environment (one Lean thread, 8192 MiB allocator limit)",
              flush=True)
        with tempfile.TemporaryDirectory(prefix="dfp-graph-extractor-") as temp:
            extractor_file = Path(temp) / "Extract.lean"
            extractor_file.write_text(original.replace(old, new))
            extractor = LeanEnvironmentExtractor(extractor_file, runner=limited_runner,
                                                 timeout_seconds=1800)
            raw = extractor.extract_project(repo_root, project)[project.project_id]
        raw_bytes = json.dumps(raw, ensure_ascii=False).encode()
    (evidence / "raw.json").write_bytes(raw_bytes)
    provenance["rawSha256"] = hashlib.sha256(raw_bytes).hexdigest()
    (evidence / "provenance.json").write_text(json.dumps(provenance, indent=2))
    raw_by_name = {item["name"]: item for item in raw}
    source_cache = {}
    head_pattern = re.compile(
        r"^[ \t]*(?:@\[[\s\S]*?\]\s*)*"
        r"(?P<modifiers>(?:(?:private|protected|public|noncomputable)\s+)*)"
        r"(?P<kind>theorem|lemma)\s+(?P<name>[^\s({:\[=]+)", re.MULTILINE)
    for name in lean_files:
        path = repo_root / name
        file = path.relative_to(project_root).as_posix()
        text = path.read_text()
        docs = {match.start("name"): match["doc"].strip()
                for match in DECL_RE.finditer(text)}
        heads = []
        for match in head_pattern.finditer(mask_comments(text)):
            heads.append(dict(line=text.count("\n", 0, match.start("kind")) + 1,
                              name=match["name"].strip("«»"),
                              private="private" in match["modifiers"],
                              doc=docs.get(match.start("name"), "")))
        source_cache[file] = heads
    selected = []
    for item in raw:
        if item["kind"] != "theorem" or item["name"].startswith("_private."):
            continue
        file = item["moduleName"].replace(".", "/") + ".lean"
        path = project_root / file
        if not path.is_file():
            raise RuntimeError(f"Unresolved source module: {item['moduleName']}")
        heads = source_cache[file]
        index = bisect_left([head["line"] for head in heads], item["line"])
        # Exclude elaborator-generated equation/proof auxiliaries at the same range.
        if index == len(heads) or heads[index]["private"] or not (
                item["name"] == heads[index]["name"] or
                item["name"].endswith("." + heads[index]["name"])):
            continue
        selected.append({**item, "file": file, "line": heads[index]["line"]})
    selected.sort(key=lambda x: (x["name"] not in MAIN_RESULTS,
                                list(MAIN_RESULTS).index(x["name"])
                                if x["name"] in MAIN_RESULTS else 0, x["name"]))
    selected_by_name = {x["name"]: x["name"] for x in selected}
    missing = MAIN_RESULTS.keys() - selected_by_name.keys()
    if missing:
        raise RuntimeError(f"Missing public main results: {sorted(missing)}")

    def section(item):
        if item["name"] in MAIN_RESULTS:
            return "Main results"
        parts = item["file"].split("/")
        if parts[0] == "DFPWolfe":
            return "Paper-facing lemmas" if parts[1].startswith("A_uniformly") else "Paper infrastructure"
        if "PlanarConvergence.lean" in parts:
            return "Planar convergence"
        if "SecantDegeneration.lean" in parts:
            return "Secant degeneration"
        if "WolfeCounterexample" in parts:
            return "Wolfe counterexample"
        return " / ".join(parts[1:3])

    sections = []
    section_ids = {}
    items = []
    for item in selected:
        group = section(item)
        if group not in section_ids:
            key = "section-" + str(len(sections))
            section_ids[group] = key
            color, wash = PALETTE[len(sections) % len(PALETTE)]
            sections.append(dict(id=key, label=group, short=group, color=color, wash=wash))
        dependencies = {}
        for field in ("statementDependencies", "proofDependencies", "dependencies"):
            dependencies[field] = [name for name in contract_dependencies(
                item["name"], raw_by_name, selected_by_name, field) if name != item["name"]]
        assert set(dependencies["dependencies"]) == (
            set(dependencies["statementDependencies"]) | set(dependencies["proofDependencies"]))
        label = MAIN_RESULTS.get(item["name"], item["name"].split(".")[-1])
        items.append(dict(id=item["name"], label=label, title=label, type="Theorem",
                          section=section_ids[group], file=item["file"], line=item["line"],
                          declaration=item["name"], statement=item["docString"],
                          dependencyEvidence="compiled", **dependencies))
    compiled_count = len(items)
    compiled_locations = {(item["file"], item["line"]) for item in items}
    source_only_count = 0
    source_count = 0
    for file, heads in source_cache.items():
        for head in heads:
            if head["private"]:
                continue
            line = head["line"]
            source_count += 1
            if (file, line) in compiled_locations:
                continue
            name = head["name"]
            group = "Source inventory (not imported)"
            if group not in section_ids:
                key = "source-only"
                section_ids[group] = key
                sections.append(dict(id=key, label=group, short=group,
                                     color="#6b7280", wash="#f3f4f6"))
            items.append(dict(id=f"source:{file}:{line}", label=name, title=name,
                              type="Theorem", section=section_ids[group], file=file, line=line,
                              declaration=name, statement=head["doc"],
                              statementDependencies=[], proofDependencies=[], dependencies=[],
                              dependencyEvidence="source-only"))
            source_only_count += 1
    data = dict(schemaVersion=2,
                project=dict(id=project.project_id, title=project_title(project), kind="papers",
                             branch="v4.32.0", commit=commit,
                             repository="https://github.com/optpku/ReasBook",
                             sourceRoot=project.source_root),
                sections=sections, items=items,
                generation=dict(mode="lean-environment", rootModule=project.root_module,
                                rawDeclarationCount=len(raw), compiledItemCount=compiled_count,
                                sourceOnlyItemCount=source_only_count,
                                sourceInventoryItemCount=source_count, mergedItemCount=len(items),
                                dependencyCoverage="partial" if source_only_count else "complete",
                                inventoryMode="source-plus-compiled",
                                dependencyModel="statement-and-proof-v1",
                                selection="All public source-declared theorems/lemmas; dependencies are available for Paper.lean's compiled environment; definitions and private/generated helpers are contracted",
                                sourceSha256=source_hash.hexdigest(), sdkSha256=sdk_hash.hexdigest(),
                                extractorSha256=hashlib.sha256(original.encode()).hexdigest(),
                                moduleOwnership=["DFP_wolfe_local", "DFPWolfe", "ReasLib"]))
    # Keep the paper/Lean view switch when refreshing this project's data.
    assets = project_root / "theorem-map"
    if not (assets / "index.html").is_file():
        assets = resources / "assets"
    copy_generic_map(assets, output, data)
    subprocess.run([sys.executable, str(Path(__file__).with_name("generate_paper_graph.py")),
                    "--graph-root", str(output)], check=True)
    print(json.dumps(dict(output=str(output), sourceCommit=commit, nodes=len(items),
                          edges=sum(len(x["dependencies"]) for x in items)), indent=2))


if __name__ == "__main__":
    main()
