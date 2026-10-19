#!/usr/bin/env python3
"""Render a paper-interface map from the SDK's compiled declaration export.

Numbered interface files can expose several existing constants with #check.
Nodes group interfaces with the same primary compiled constant. Every edge is
contracted from the checked constants' actual statement/proof dependencies;
helper constants and numeric certificates are not shown as separate nodes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

from theorem_graph_sdk.analysis import PALETTE
from theorem_graph_sdk.generator import RESOURCE_ROOT
from theorem_graph_sdk.render import copy_generic_map


def checked_constants(source: str, declarations: dict) -> list[str]:
    """Resolve the checked project constants in source order."""
    code = re.sub(r"/-.*?-/", "", source, flags=re.S)
    namespace = []
    found = []
    active = False
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("namespace "):
            namespace.append(stripped.split()[1])
            active = False
        elif stripped.startswith("end"):
            if namespace:
                namespace.pop()
            active = False
        elif stripped.startswith("#check"):
            active = True
        elif re.match(r"(?:(?:public|private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|variable|open|universe)\b", stripped):
            active = False
        if not active:
            continue
        for token in re.findall(r"\b[A-Za-z_][A-Za-z0-9_'.]*", line):
            options = [token] + [".".join(namespace[:i] + [token])
                                 for i in range(len(namespace), 0, -1)]
            name = next((value for value in options if value in declarations), None)
            if name is not None and name not in found:
                found.append(name)
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    exported = json.loads(args.raw.read_text())
    assert len(exported) == 1 and exported[0]["id"] == root.name
    raw = {entry["name"]: entry for entry in exported[0]["declarations"]}
    assert raw and all("proofDependencies" in entry for entry in raw.values())
    modules = re.findall(r"^public import (\S+)", (root / "GlowinskiADMM.lean").read_text(), re.M)
    grouped = {}
    for module in modules:
        file = Path(*module.split(".")[1:]).with_suffix(".lean")
        source = (root / file).read_text()
        members = checked_constants(source, raw)
        owned = [d for d in raw.values() if d["moduleName"] == module and d["kind"] == "theorem"
                 and not d["name"].startswith("_private")]
        labelled = [d for d in owned if re.match(r"^(Corollary|Lemma|Proposition) \d", d["docString"])
                    or "prop:finite" in d["docString"]]
        if labelled:
            members.insert(0, labelled[0]["name"])
        assert members, f"No compiled interface constants: {module}"
        members = list(dict.fromkeys(members))
        primary = members[0]
        match = re.fullmatch(r"([a-z]+)_([0-9_]+)", file.stem)
        if match:
            kind, number = match.groups()
            number = number.replace("_", ".")
            label = f"{kind.title()} {number}"
        else:
            kind, number, label = "proposition", "finite", "Proposition prop:finite"
        comments = [text.strip().lstrip("!-").strip() for text in re.findall(r"/-(.*?)-/", source, re.S)]
        statements = [text for text in comments if re.match(r"(?i)^" + kind + r" \d", text)
                      or "prop:finite" in text]
        assert statements, f"Missing source statement: {file}"
        node = grouped.setdefault(primary, dict(
            id=f"{kind}-{number.replace('.', '-')}", label=label, title=label, type=kind.title(),
            section="section-" + number.split(".")[0], file=file.as_posix(),
            line=labelled[0]["line"] if labelled else source[:source.index("#check")].count("\n") + 1,
            declaration=primary, statement="", interfaceDeclarations=[], interfaces=[], dependencyEvidence="compiled"))
        node["interfaces"].append(dict(label=label, file=file.as_posix()))
        if label != node["label"]:
            node["label"] += " / " + label
            node["title"] = node["label"]
        node["statement"] += ("\n\n" if node["statement"] else "") + "\n\n".join(statements)
        node["interfaceDeclarations"] = list(dict.fromkeys(node["interfaceDeclarations"] + members))
    nodes = list(grouped.values())
    owners = {}
    for node in sorted(nodes, key=lambda n: len(n["interfaceDeclarations"]), reverse=True):
        for name in node["interfaceDeclarations"]:
            owners[name] = node["id"]
    owners.update({node["declaration"]: node["id"] for node in nodes})

    def dependencies(node, field):
        pending = [dep for name in node["interfaceDeclarations"] for dep in raw[name][field]]
        seen = set(node["interfaceDeclarations"])
        result = set()
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if name in owners and owners[name] != node["id"]:
                result.add(owners[name])
            elif name in raw:
                pending.extend(raw[name][field])
        return sorted(result)

    for node in nodes:
        node["statementDependencies"] = dependencies(node, "statementDependencies")
        node["proofDependencies"] = dependencies(node, "proofDependencies")
        node["dependencies"] = sorted(set(node["statementDependencies"] + node["proofDependencies"]))
    sections = []
    for section in dict.fromkeys(node["section"] for node in nodes):
        color, wash = PALETTE[len(sections) % len(PALETTE)]
        label = "Finite objectives" if section == "section-finite" else "Section " + section.split("-")[1]
        sections.append(dict(id=section, label=label, short=label, color=color, wash=wash))
    data = dict(schemaVersion=2, project=dict(id=root.name,
        title="The multiplier step size of two-block ADMM: convergence and counterexamples",
        kind="papers", branch="v4.32.0", commit=args.commit,
        repository="https://github.com/optpku/ReasBook", sourceRoot=f"ReasBook/Papers/{root.name}/"),
        sections=sections, items=nodes, generation=dict(mode="lean-environment",
        rootModule=exported[0]["rootModule"], rawDeclarationCount=len(raw),
        dependencyCoverage="complete", dependencyModel="checked-public-interface-contraction-v1",
        interfaceCount=len(modules), compiledItemCount=len(nodes), sourceOnlyItemCount=0,
        rawSha256=hashlib.sha256(args.raw.read_bytes()).hexdigest(),
        grouping="Interfaces with the same primary compiled constant share a node; all aliases are listed."))
    copy_generic_map(RESOURCE_ROOT / "assets", args.output, data)
    print(json.dumps(dict(nodes=len(nodes), edges=sum(len(n["dependencies"]) for n in nodes),
                          interfaces=len(modules)), indent=2))


if __name__ == "__main__":
    main()
