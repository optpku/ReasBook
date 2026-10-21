#!/usr/bin/env python3
"""Regenerate bilingual README resource columns from verified public resources.

This is a maintenance tool, not a CI runtime dependency.  It preserves the
manually curated title/source/contributor columns and only replaces the final
column of the Books and Papers tables in each language.
"""

from __future__ import annotations

import re
from pathlib import Path

from urllib.parse import urlsplit

from project_catalog import EXCLUDED_PROJECTS, NO_VERSO_PROJECTS


SITE_BASE = "https://reasbook.reaslab.io/artifacts"
REVIEWER_BASE = "https://reasbook.reaslab.io/review"
# Verified deployment entry points (2026-10-22), relative to each project's
# docs/ directory. Build outputs use different module roots across toolchains.
PUBLISHED_DOCS = {
    ("books", "AlgebraicTopology_May_1999"): "ReasBook/AlgebraicTopology_May_1999/Book.html",
    ("books", "Analysis2_Tao_2022"): "ReasBook/Analysis2_Tao_2022/Book.html",
    ("books", "CombinatorialGroupTheory_Magnus_2004"): "ReasBook/CombinatorialGroupTheory_Magnus_2004/Book.html",
    ("books", "ConvexAnalysis_Rockafellar_1970"): "ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html",
    ("books", "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017"): "ReasBook/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html",
    ("books", "FirstOrderMethodsOptimization_Beck_2017"): "ReasBook/FirstOrderMethodsOptimization_Beck_2017/Book.html",
    ("books", "IntegerProgramming_Conforti_2014"): "ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html",
    ("books", "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025"): "ReasBook/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html",
    ("books", "IntroductoryLecturesOnConvexOptimization_Nesterov_2004"): "ReasBook/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html",
    ("books", "OptimizationTheoryAndMethods_SunYuan_2006"): "ReasBook/OptimizationTheoryAndMethods_SunYuan_2006/Book.html",
    ("books", "RiemannSurfaces_Forster_1981"): "ReasBook/RiemannSurfaces_Forster_1981/Book.html",
    ("papers", "BFGSMinimumQOrder_Liu_2026"): "ReasBook/Paper.html",
    ("papers", "DFP_wolfe_local"): "ReasBook/DFP_wolfe_local/Paper.html",
    ("papers", "OnSomeLocalRings_Maassaran_2025"): "ReasBook/OnSomeLocalRings_Maassaran_2025/Paper.html",
    ("papers", "RockafellarSum_2026"): "ReasBook/RockafellarSum_2026/Paper.html",
    ("papers", "SmoothMinimization_Nesterov_2004"): "ReasBook/SmoothMinimization_Nesterov_2004/Paper.html",
    ("papers", "TR_LALM_theory"): "ReasBook/TR_LALM_theory.html",
}
PUBLISHED_THEOREM_MAPS = set(PUBLISHED_DOCS) - {
    ("books", "IntegerProgramming_Conforti_2014"),
    ("papers", "RockafellarSum_2026"),
}
UNPUBLISHED_DOCUMENTATION = {("papers", "glowinski_admm_counterexample")}
README_LANGUAGES = {
    "README.md": "en",
    "README.zh-CN.md": "zh-CN",
}
RESOURCE_LABELS = {
    "en": {
        "docs": "Docs",
        "theorem_map": "Theorem map",
        "source_only": "Source only (excluded from the current release profile)",
        "verso_unpublished": "Verso not published",
        "documentation_pending": "Source available; Docs, Verso and theorem map pending publication",
    },
    "zh-CN": {
        "docs": "文档",
        "theorem_map": "定理依赖图",
        "source_only": "仅源代码（不包含在当前发布配置中）",
        "verso_unpublished": "尚未发布 Verso",
        "documentation_pending": "源代码可用；Docs、Verso 和定理依赖图待发布",
    },
}


def resource_cell(project: dict[str, str], *, language: str = "en") -> str:
    name = project["name"]
    slug = project["slug"]
    kind = project["kind"]
    labels = RESOURCE_LABELS[language]

    if (kind, name) in UNPUBLISHED_DOCUMENTATION:
        return labels["documentation_pending"]

    if name in EXCLUDED_PROJECTS or (kind, name) not in PUBLISHED_DOCS:
        return labels["source_only"]

    project_base = f"{SITE_BASE}/projects/{slug}"
    docs_href = f"{project_base}/docs/{PUBLISHED_DOCS[(kind, name)]}"

    pieces = [f"[{labels['docs']}]({docs_href})"]
    if name not in NO_VERSO_PROJECTS:
        pieces.append(f"[Verso]({project_base}/)")
    else:
        pieces.append(labels["verso_unpublished"])

    if (kind, name) in PUBLISHED_THEOREM_MAPS:
        pieces.append(
            f"[{labels['theorem_map']}]({project_base}/theorem-maps/{kind}/{slug}/)"
        )
    pieces.append(f"[Reviewer]({REVIEWER_BASE}/books/{slug}/)")

    # Use an entity so the separator is rendered inside the Markdown table
    # cell instead of being parsed as another table column.
    return " &#124; ".join(pieces)


def update_resource_cells(
    readme: Path,
    projects: dict[tuple[str, str], dict[str, str]],
    *,
    language: str,
) -> int:
    lines = readme.read_text(encoding="utf-8").splitlines()
    project_ref = re.compile(r"ReasBook/(Books|Papers)/([A-Za-z0-9_]+)/")

    changed = 0
    for index, line in enumerate(lines):
        if not line.startswith("| **["):
            continue
        match = project_ref.search(line)
        if not match:
            continue
        kind = "books" if match.group(1) == "Books" else "papers"
        name = match.group(2)
        project = projects.get((kind, name))
        if project is None:
            continue

        # A paper can have independently curated proof routes below its title.
        # Their entry modules and reading sections are more specific than the
        # aggregate project resources returned by resource_cell.
        following = index + 1
        proof_routes = []
        while following < len(lines) and lines[following].startswith("| ↳ **"):
            proof_routes.append(lines[following])
            following += 1
        if proof_routes and all(
            len(row.split("|")) == 6
            and (reference := project_ref.search(row)) is not None
            and reference.groups() == match.groups()
            for row in proof_routes
        ):
            continue

        cells = line.split("|")
        if len(cells) != 6:
            continue
        # The last cell can also contain original papers and source notes.
        # Keep those links when regenerating hosted reading resources.
        references = [
            link for link in re.findall(r"\[[^\]]+\]\([^)]+\)", cells[4])
            if not re.match(r"\[(?:Docs|文档|Verso|Theorem map|定理依赖图|Reviewer)\]", link)
            and urlsplit(link.split("](", 1)[1][:-1]).hostname not in {
                "optpku.github.io", "reasbook.reaslab.io", "reasbook-reviewer.reaslab.io",
            }
        ]
        resources = [resource_cell(project, language=language), *references]
        new_resources = " " + " &#124; ".join(resources) + " "
        if cells[4] != new_resources:
            cells[4] = new_resources
            lines[index] = "|".join(cells)
            changed += 1

    if changed:
        readme.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return changed


def main() -> None:
    repo_root = Path.cwd()
    # Reading links follow the deployed inventory, independently of which
    # version branches happen to be fetched in this checkout.
    projects = {
        (kind, name): {"kind": kind, "name": name, "slug": name.lower()}
        for kind, name in PUBLISHED_DOCS
    }
    # Keep excluded source-only entries present in the table.
    for kind, name, kind_title in (
        ("books", "ProbabilityTheory_Klenke_2020", "Books"),
        ("books", "ComputationalMethodsInverseProblems_Vogel_2002", "Books"),
    ):
        projects[(kind, name)] = {
            "kind": kind,
            "kindTitle": kind_title,
            "name": name,
            "slug": name.lower(),
            "branch": "",
        }

    changes = {
        filename: update_resource_cells(
            repo_root / filename,
            projects,
            language=language,
        )
        for filename, language in README_LANGUAGES.items()
    }
    changed = sum(changes.values())
    if changed:
        summary = ", ".join(
            f"{filename}: {count}" for filename, count in changes.items()
        )
        print(f"Updated {changed} resource cells ({summary})")
    else:
        print("No resource cells changed")


if __name__ == "__main__":
    main()
