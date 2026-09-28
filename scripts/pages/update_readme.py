#!/usr/bin/env python3
"""Regenerate bilingual README resource columns from the project catalog.

This is a maintenance tool, not a CI runtime dependency.  It preserves the
manually curated title/source/contributor columns and only replaces the final
column of the Books and Papers tables in each language.
"""

from __future__ import annotations

import re
from pathlib import Path

from project_catalog import (
    EXCLUDED_PROJECTS,
    NO_VERSO_PROJECTS,
    discover_projects,
    existing_branches,
    load_registry_branches,
)


SITE_BASE = "https://optpku.github.io/ReasBook"
# Only link graphs already published at stable per-project URLs.
PUBLISHED_THEOREM_MAPS = {("papers", "DFP_wolfe_local"), ("papers", "TR_LALM_theory")}
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
    },
    "zh-CN": {
        "docs": "文档",
        "theorem_map": "定理依赖图",
        "source_only": "仅源代码（不包含在当前发布配置中）",
        "verso_unpublished": "尚未发布 Verso",
    },
}


def resource_cell(project: dict[str, str], *, language: str = "en") -> str:
    name = project["name"]
    slug = project["slug"]
    kind = project["kind"]
    labels = RESOURCE_LABELS[language]

    if name in EXCLUDED_PROJECTS:
        return labels["source_only"]

    if kind == "books":
        docs_href = f"{SITE_BASE}/docs/ReasBook/Books/{name}/Book.html"
    else:
        docs_href = f"{SITE_BASE}/docs/ReasBook/Papers/{name}/Paper.html"

    pieces = [f"[{labels['docs']}]({docs_href})"]
    if name not in NO_VERSO_PROJECTS:
        pieces.append(f"[Verso]({SITE_BASE}/sites/{slug}/pages/)")
    else:
        pieces.append(labels["verso_unpublished"])

    if (kind, name) in PUBLISHED_THEOREM_MAPS:
        pieces.append(
            f"[{labels['theorem_map']}]({SITE_BASE}/theorem-maps/{kind}/{slug}/)"
        )

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

        cells = line.split("|")
        if len(cells) != 6:
            continue
        new_resources = f" {resource_cell(project, language=language)} "
        if cells[4] != new_resources:
            cells[4] = new_resources
            lines[index] = "|".join(cells)
            changed += 1

    if changed:
        readme.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return changed


def main() -> None:
    repo_root = Path.cwd()
    branches = existing_branches(
        [record["version"] for record in load_registry_branches(repo_root)],
        repo_root,
    )
    _, discovered = discover_projects(branches, repo_root)
    projects = {(project["kind"], project["name"]): project for project in discovered}
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
