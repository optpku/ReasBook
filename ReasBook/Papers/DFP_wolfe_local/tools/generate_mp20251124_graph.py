#!/usr/bin/env python3
"""Generate the paper-numbered DAG for the 20251124 manuscript."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from extract_paper_statements import extract, render


RESULTS = [
    ("mp24-theorem-1", "Theorem 1", "General strong-Wolfe counterexample", "thm:main", "main", "DFPWolfe.MP20251124.theorem1", ["mp24-theorem-4", "mp24-lemma-10", "mp24-lemma-11"], "Results.lean", "theorem1"),
    ("mp24-theorem-2", "Theorem 2", "Planar convergence with a locally Lipschitz Hessian", "thm:planar-convergence", "convergence", "DFPWolfe.MP20251124.theorem2", ["mp24-lemma-13"], "Results.lean", "theorem2"),
    ("mp24-lemma-3", "Lemma 3", "Exact polar search step, curvature, and DFP update", "lem:polar-dfp", "construction", "DFPWolfe.MP20251124.lemma3_positiveStep_iff", [], "Results.lean", "lemma3_positiveStep_iff"),
    ("mp24-theorem-4", "Theorem 4", "Fixed recurrence and a general existence witness (partial)", "thm:concrete", "main", "DFPWolfe.MP20251124.theorem4_concrete", ["mp24-lemma-3", "mp24-lemma-5", "mp24-lemma-6", "mp24-lemma-7", "mp24-lemma-8", "mp24-lemma-9"], "Results.lean", "theorem4_concrete"),
    ("mp24-lemma-5", "Lemma 5", "Limit of a single scaled DFP step", "lem:fixed-single-limit", "construction", "DFPWolfe.MP20251124.SingleStepLimit.singleStepLimitMatrix", [], "SingleStepLimit.lean", "singleStepLimitMatrix"),
    ("mp24-lemma-6", "Lemma 6", "Fixed-cycle derivative and reference contraction (partial)", "lem:fixed-cycle", "construction", "DFPWolfe.MP20251124.FixedCycle.restoringDerivative", ["mp24-lemma-5"], "FixedCycle.lean", "restoringDerivative"),
    ("mp24-lemma-7", "Lemma 7", "Generalized polar continuation support", "lem:fixed-continuation", "construction", "DFPWolfe.MP20251124.lemma7_fixedContinuation", ["mp24-lemma-6"], "Results.lean", "lemma7_fixedContinuation"),
    ("mp24-lemma-8", "Lemma 8", "Generalized geometric estimates (fixed Wolfe margins pending)", "lem:fixed-geometry", "construction", "DFPWolfe.MP20251124.lemma8_fixedGeometry", ["mp24-lemma-3", "mp24-lemma-7"], "Results.lean", "lemma8_fixedGeometry"),
    ("mp24-lemma-9", "Lemma 9", "Generalized objective realization support", "lem:fixed-realization", "construction", "DFPWolfe.MP20251124.lemma9_fixedRealization", ["mp24-lemma-8"], "Results.lean", "lemma9_fixedRealization"),
    ("mp24-lemma-10", "Lemma 10", "General Wolfe reference family", "lem:general-reference", "generalization", "DFPWolfe.MP20251124.lemma10_generalReference", ["mp24-lemma-5"], "Results.lean", "lemma10_generalReference"),
    ("mp24-lemma-11", "Lemma 11", "General Hölder continuation", "lem:general-continuation", "generalization", "DFPWolfe.MP20251124.lemma11_generalContinuation", ["mp24-lemma-6", "mp24-lemma-10"], "Results.lean", "lemma11_generalContinuation"),
    ("mp24-corollary-12", "Corollary 12", "Identity initialization", "cor:identity-initialization", "main", "DFPWolfe.MP20251124.corollary12_identityInitialization", ["mp24-theorem-1"], "Results.lean", "corollary12_identityInitialization"),
    ("mp24-lemma-13", "Lemma 13", "Planar secant degeneration", "lem:planar-degeneration", "convergence", "DFPWolfe.MP20251124.lemma13_planarDegeneration", [], "Results.lean", "lemma13_planarDegeneration"),
]


SUPPORT = {
    "mp24-lemma-3": [("Results.lean", name) for name in (
        "lemma3_stepFormulaAndUniqueness", "lemma3_polarSecantPairing_pos", "lemma3_polarInverseUpdate")],
    "mp24-theorem-4": [("FixedRecurrence.lean", "initialData"), ("FixedRecurrence.lean", "normalizedState_succ")],
    "mp24-lemma-6": [("FixedCycle.lean", name) for name in (
        "referenceStages", "map_analyticAt", "transverseDerivative", "referenceContraction")],
}


def locate_decl(path: Path, short_name: str) -> tuple[int, str]:
    lines = path.read_text().splitlines(keepends=True)
    pattern = re.compile(r"\b(?:theorem|lemma)\s+" + re.escape(short_name) + r"\b")
    for index, line in enumerate(lines):
        if pattern.search(line):
            end = len(lines)
            for next_index in range(index + 1, len(lines)):
                if re.match(r"^(?:/--|end(?:\s|$)|\s*(?:theorem|lemma|def|structure)\s+)", lines[next_index]):
                    end = next_index
                    break
            return index + 1, "".join(lines[index:end]).rstrip()
    raise ValueError(f"declaration not found: {short_name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manuscript", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--aux", type=Path, required=True, help="LaTeX label numbers for this manuscript")
    parser.add_argument("--renderer", nargs="+", required=True, help="KaTeX renderer command")
    args = parser.parse_args()

    manuscript = args.manuscript.read_text()
    mapping = {"items": [{"id": row[0], "label": row[1], "texLabel": row[3]} for row in RESULTS]}
    statements = extract(manuscript, args.aux.read_text(), mapping)
    formula_count = render(statements, args.renderer)

    manuscript_digest = hashlib.sha256(args.manuscript.read_bytes()).hexdigest()
    items = []
    for index, (item_id, label, title, tex_label, section, declaration, dependencies, filename, short_name) in enumerate(RESULTS):
        typeset = statements[index]
        statement = typeset["statementLatex"]
        start_line = typeset["sourceStartLine"]
        end_line = typeset["sourceEndLine"]
        source_file = args.source_root / "Papers/DFP_wolfe_local/DFPWolfe/MP20251124" / filename
        line, code = locate_decl(source_file, short_name)
        relative_file = source_file.relative_to(args.source_root).as_posix()
        declaration_entry = {"declaration": declaration, "file": relative_file, "line": line}
        excerpt = {**declaration_entry, "leanCode": code}
        excerpts = [excerpt]
        declarations = [declaration_entry]
        for other_file, other_name in SUPPORT.get(item_id, []):
            other_path = source_file.parent / other_file
            other_line, other_code = locate_decl(other_path, other_name)
            namespace = "DFPWolfe.MP20251124"
            if other_file != "Results.lean":
                namespace += "." + Path(other_file).stem
            entry = {"declaration": namespace + "." + other_name,
                     "file": other_path.relative_to(args.source_root).as_posix(), "line": other_line}
            declarations.append(entry)
            excerpts.append({**entry, "leanCode": other_code})
        items.append({
            "id": item_id,
            "label": label,
            "title": title,
            "type": label.split()[0],
            "section": section,
            "declaration": declaration,
            "file": relative_file,
            "line": line,
            "endLine": line + code.count("\n"),
            "statement": statement,
            "statementHtml": typeset["statementHtml"],
            "statementSha256": hashlib.sha256(statement.encode()).hexdigest(),
            "statementSource": {"manuscript": "20251124-DFP/MP.zip/main.tex", "manuscriptSha256": manuscript_digest, "startLine": start_line, "endLine": end_line},
            "texLabel": tex_label,
            "paperMapping": label,
            "relatedDeclarations": declarations,
            "leanExcerpts": excerpts,
            "dependencies": dependencies,
            "statementDependencies": [],
            "proofDependencies": [],
            "dependencyEvidence": "curated-paper-dependencies",
            "sourceSha256": hashlib.sha256(source_file.read_bytes()).hexdigest(),
        })

    sections = [
        {"id": "construction", "label": "Fixed polar construction", "short": "Construction", "color": "#23745d", "wash": "#e4f2ed"},
        {"id": "generalization", "label": "Generalization", "short": "Generalization", "color": "#a35c26", "wash": "#f8eee2"},
        {"id": "main", "label": "Main results", "short": "Main results", "color": "#315fb5", "wash": "#e9effa"},
        {"id": "convergence", "label": "Convergence", "short": "Convergence", "color": "#7654a6", "wash": "#eee8f8"},
    ]
    project = {"id": "DFP_wolfe_local", "title": "DFP 20251124 polar proof", "kind": "papers", "branch": "v4.32.0", "commit": args.commit, "repository": "https://github.com/optpku/ReasBook", "sourceRoot": "ReasBook"}
    edge_witnesses = []
    evidence = {
        "mp24-theorem-1": (1455, 1560), "mp24-theorem-2": (1665, 1720),
        "mp24-theorem-4": (520, 530), "mp24-lemma-5": (573, 620),
        "mp24-lemma-6": (683, 710), "mp24-lemma-7": (808, 850),
        "mp24-lemma-8": (880, 1080), "mp24-lemma-9": (1099, 1190),
        "mp24-lemma-10": (1274, 1348), "mp24-lemma-11": (1376, 1453),
        "mp24-corollary-12": (1594, 1630), "mp24-lemma-13": (1665, 1720),
        "mp24-lemma-3": (335, 355),
    }
    for item in items:
        for dependency in item["dependencies"]:
            start, end = evidence[item["id"]]
            edge_witnesses.append({"source": dependency, "target": item["id"], "evidence": "curated-paper-proof", "manuscript": "20251124-DFP/MP.zip/main.tex", "manuscriptSha256": manuscript_digest, "startLine": start, "endLine": end, "reason": "The proof block explicitly invokes the preceding construction or estimate."})
    generation = {"mode": "curated-paper-numbered", "rootModule": "DFPWolfe.MP20251124.Paper", "curatedItemCount": len(items), "sourceInventoryItemCount": len(items), "sourceOnlyItemCount": 0, "mergedItemCount": len(items), "dependencyCoverage": "reviewed-paper-dependencies", "dependencyModel": "curated-paper-proof-v2", "scope": "20251124-DFP/MP.zip; theorem-like blocks follow the manuscript source order.", "sourceSnapshot": args.commit, "manuscriptSha256": manuscript_digest, "numbering": "Shared theorem counter in the manuscript source order; 13 theorem-like results.", "edges": len(edge_witnesses), "nodes": len(items)}
    data = {"schemaVersion": 2, "project": project, "sections": sections, "items": items, "generation": generation, "edgeWitnesses": edge_witnesses}
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "data.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    overview = {**data, "generation": {**generation, "view": "paper-numbered", "selection": "All theorem-like results in 20251124-DFP/MP.zip/main.tex, in source order."}}
    (args.output / "overview-data.json").write_text(json.dumps(overview, ensure_ascii=False, indent=2) + "\n")
    (args.output / "metadata.json").write_text(json.dumps({"schemaVersion": 1, "project": project, "nodes": len(items), "edges": len(edge_witnesses), "generation": generation}, ensure_ascii=False, indent=2) + "\n")
    (args.output / "release-context.json").write_text(json.dumps({"schemaVersion": 1, "project": project, "generation": generation}, ensure_ascii=False, indent=2) + "\n")
    (args.output / "numbering.json").write_text(json.dumps({"manuscript": "20251124-DFP/MP.zip/main.tex", "manuscriptSha256": manuscript_digest, "counter": "shared theorem counter in source order", "results": [[item["label"], item["texLabel"]] for item in items]}, ensure_ascii=False, indent=2) + "\n")
    paper = {"schemaVersion": 1, "manuscriptName": "20251124-DFP/MP.zip/main.tex", "manuscriptSha256": manuscript_digest, "referenceNumbering": "Shared theorem counter in source order.", "formulaCount": formula_count, "rendering": "Pandoc with static KaTeX HTML and MathML.", "items": statements}
    (args.output / "paper-statements.json").write_text(json.dumps(paper, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"nodes": len(items), "edges": len(edge_witnesses), "manuscriptSha256": manuscript_digest}, ensure_ascii=False))


if __name__ == "__main__":
    main()
