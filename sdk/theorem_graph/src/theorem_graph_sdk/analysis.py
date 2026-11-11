"""Pure declaration parsing and dependency contraction algorithms."""

from __future__ import annotations

import json
import re
from dataclasses import replace
from pathlib import Path
from typing import Any, Iterable

from .errors import GraphConfigError
from .models import Candidate, Project


LABEL_RE = re.compile(
    r"^\s*(?:Chapter\s*\d+\s+)?(?P<kind>Assumption|Algorithm|Definition|Lemma|Theorem|"
    r"Proposition|Corollary|Remark|Example|Exercise)\s+"
    r"(?P<number>(?:(?:[A-Z]\.)?\d+(?:[._-]\d+)*|[A-Z](?:\.\d+)+)(?:[-_]extra[-_]\d+)?)",
    re.IGNORECASE,
)
DECL_RE = re.compile(
    r"/--(?P<doc>.*?)\-/\s*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+|public\s+|unsafe\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"(?P<name>[^\s({:\[=]+)",
    re.DOTALL,
)
NATURAL_PART_RE = re.compile(r"(\d+)")
TITLE_PAREN_RE = re.compile(r"^\s*\(([^)]+)\)")
SECTION_FILE_RE = re.compile(r"^(?:section|sec)[_-]?(\d+)", re.IGNORECASE)
CHAPTER_RE = re.compile(r"^chap(?:ter)?[_-]?(\d+)$", re.IGNORECASE)

PALETTE = (
    ("#315fb5", "#e9effa"),
    ("#23745d", "#e4f2ed"),
    ("#a14d3d", "#f8eae6"),
    ("#9a6a12", "#fbf1d8"),
    ("#7654a6", "#eee8f8"),
    ("#28768a", "#e2f1f4"),
)


def natural_key(value: str) -> tuple[tuple[int, object], ...]:
    """Return a total ordering key that handles mixed numeric/text pieces."""

    return tuple(
        (0, int(part)) if part.isdigit() else (1, part.lower())
        for part in NATURAL_PART_RE.split(value)
        if part
    )


def slugify(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    return slug or "item"


def normalize_label(kind: str, number: str) -> tuple[str, str, str]:
    canonical_kind = kind[0].upper() + kind[1:].lower()
    canonical_number = number.replace("_", ".")
    label = f"{canonical_kind} {canonical_number}"
    return label, slugify(label), canonical_kind


def clean_title_text(value: str) -> str:
    value = re.sub(r"`([^`]*)`", r"\1", value)
    value = re.sub(r"\[([^]]+)\]\([^)]+\)", r"\1", value)
    value = re.sub(r"\s+", " ", value).strip(' :%-."')
    if len(value) > 120:
        value = value[:117].rstrip() + "..."
    return value


def title_from_doc(doc: str, match: re.Match[str], label: str) -> str:
    rest = doc[match.end() :].lstrip()
    parenthetical = TITLE_PAREN_RE.match(rest)
    if parenthetical:
        proposed = clean_title_text(parenthetical.group(1))
        if re.search(r"[A-Za-z]", proposed) and not re.fullmatch(
            r"(?:part\s*)?[ivx\d]+", proposed, re.IGNORECASE
        ):
            return proposed
        rest = rest[parenthetical.end() :].lstrip()
    rest = rest.lstrip(":.- ")
    first = re.split(r"\n\s*\n|(?<=[.!?])\s+", rest, maxsplit=1)[0]
    return clean_title_text(first) or label


def project_title(project: Project) -> str:
    readme = project.root / "README.md"
    if readme.is_file():
        try:
            for line in readme.read_text(encoding="utf-8").splitlines():
                if line.startswith("# "):
                    return line[2:].strip()
        except OSError:
            pass
    return project.project_id.replace("_", " ")


def _module_parts(module: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    quoted = False
    for char in module:
        if char == "«":
            quoted = True
        elif char == "»":
            quoted = False
        if char == "." and not quoted:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    parts.append("".join(current))
    return [part.replace("«", "").replace("»", "") for part in parts if part]


def module_relative_file(project: Project, module_name: str) -> str:
    parts = _module_parts(module_name)
    try:
        index = parts.index(project.project_id)
    except ValueError:
        return ""
    suffix = parts[index + 1 :]
    if not suffix:
        return ""
    candidate = Path(*suffix).with_suffix(".lean")
    if (project.root / candidate).is_file():
        return candidate.as_posix()
    expected_tail = "/".join(suffix).lower() + ".lean"
    try:
        files = list(project.root.rglob(f"{suffix[-1]}.lean"))
    except OSError:
        files = []
    for file in files:
        relative = file.relative_to(project.root).as_posix()
        if relative.lower().endswith(expected_tail):
            return relative
    if len(files) == 1:
        return files[0].relative_to(project.root).as_posix()
    return candidate.as_posix()


def section_for(relative_file: str, number: str) -> tuple[str, str]:
    parts = Path(relative_file).parts
    for part in parts:
        chapter = CHAPTER_RE.match(part)
        if chapter:
            value = str(int(chapter.group(1)))
            return f"chapter-{value}", f"Chapter {value}"
    for part in reversed(parts):
        section = SECTION_FILE_RE.match(Path(part).stem)
        if section:
            value = str(int(section.group(1)))
            return f"section-{value}", f"Section {value}"
    first = re.match(r"(?:[A-Z]\.)?(\d+)", number, re.IGNORECASE)
    if first:
        value = str(int(first.group(1)))
        return f"section-{value}", f"Section {value}"
    appendix = re.match(r"([A-Z])\.", number, re.IGNORECASE)
    if appendix:
        value = appendix.group(1).upper()
        return f"appendix-{value.lower()}", f"Appendix {value}"
    return "overview", "Overview"


def candidate_score(
    label: str,
    item_type: str,
    doc: str,
    declaration_kind: str,
    relative_file: str,
    line: int,
) -> float:
    normalized_label = re.sub(r"[^a-z0-9]", "", label.lower())
    normalized_stem = re.sub(r"[^a-z0-9]", "", Path(relative_file).stem.lower())
    score = min(len(doc), 6000) / 100.0
    if normalized_stem == normalized_label:
        score += 500
    elif normalized_label in normalized_stem:
        score += 180
    first_paragraph = doc[:500].lower()
    if "source-facing" in first_paragraph:
        score += 120
    if "main statement" in first_paragraph or "main theorem" in first_paragraph:
        score += 60
    if "helper" in first_paragraph or "intermediate" in first_paragraph:
        score -= 100
    if item_type in {
        "Theorem",
        "Lemma",
        "Proposition",
        "Corollary",
    } and declaration_kind in {
        "theorem",
        "opaque",
    }:
        score += 30
    score += min(line, 100000) / 1_000_000
    return score


def candidates_from_raw(
    project: Project, declarations: Iterable[dict[str, Any]]
) -> list[Candidate]:
    candidates: list[Candidate] = []
    for declaration in declarations:
        doc = str(declaration.get("docString") or "").strip()
        match = LABEL_RE.match(doc)
        if not match:
            continue
        label, item_id, item_type = normalize_label(
            match.group("kind"), match.group("number")
        )
        number = match.group("number").replace("_", ".").replace("-", ".")
        module_name = str(declaration.get("moduleName") or "")
        relative_file = module_relative_file(project, module_name)
        try:
            line = int(declaration.get("line") or 1)
        except (TypeError, ValueError):
            line = 1
        section_id, section_label = section_for(relative_file, number)
        declaration_kind = str(declaration.get("kind") or "")
        candidates.append(
            Candidate(
                label=label,
                item_id=item_id,
                item_type=item_type,
                number=number,
                title=title_from_doc(doc, match, label),
                statement=doc,
                declaration=str(declaration.get("name") or ""),
                declaration_kind=declaration_kind,
                module_name=module_name,
                relative_file=relative_file,
                line=line,
                section_id=section_id,
                section_label=section_label,
                score=candidate_score(
                    label, item_type, doc, declaration_kind, relative_file, line
                ),
            )
        )
    return candidates


def fallback_raw_declarations(project: Project) -> list[dict[str, Any]]:
    """Extract labelled declarations from source when no compiled env exists."""

    declarations: list[dict[str, Any]] = []
    for file in sorted(project.root.rglob("*.lean"), key=lambda path: path.as_posix()):
        try:
            text = file.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        relative = file.relative_to(project.root)
        module_suffix = ".".join(relative.with_suffix("").parts)
        module_name = f"{project.project_id}.{module_suffix}"
        for match in DECL_RE.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            declarations.append(
                {
                    "name": match.group("name"),
                    "moduleName": module_name,
                    "line": line,
                    "kind": match.group("kind"),
                    "docString": match.group("doc").strip(),
                    "statementDependencies": [],
                    "proofDependencies": [],
                    "dependencies": [],
                }
            )
    return declarations


def select_representatives(candidates: Iterable[Candidate]) -> list[Candidate]:
    groups: dict[str, list[Candidate]] = {}
    for candidate in candidates:
        groups.setdefault(candidate.item_id, []).append(candidate)
    selected = [
        max(
            group,
            key=lambda item: (
                item.score,
                -item.line,
                item.relative_file,
                item.declaration,
            ),
        )
        for group in groups.values()
    ]
    selected.sort(
        key=lambda item: natural_key(
            f"{item.relative_file}:{item.line:08d}:{item.label}"
        )
    )
    return selected


def contract_dependencies(
    declaration: str,
    raw_by_name: dict[str, dict[str, Any]],
    selected_by_name: dict[str, str],
    dependency_field: str = "dependencies",
) -> list[str]:
    """Contract helper declarations until the nearest selected items.

    ``dependency_field`` selects the dependency class on the starting
    declaration. Once traversal enters an unselected helper, its complete
    dependency union is followed. This preserves whether a literature-level
    edge originated in the statement or proof/body without losing a path that
    crosses an implementation helper.
    """

    def values(item: dict[str, Any], field: str) -> list[Any]:
        explicit = item.get(field)
        if isinstance(explicit, list):
            return explicit
        if field == "dependencies":
            statement = item.get("statementDependencies")
            proof = item.get("proofDependencies")
            return [
                *(statement if isinstance(statement, list) else []),
                *(proof if isinstance(proof, list) else []),
            ]
        return []

    result: set[str] = set()
    visited: set[str] = set()
    stack = list(values(raw_by_name.get(declaration, {}), dependency_field))
    while stack:
        current = str(stack.pop())
        if current in visited:
            continue
        visited.add(current)
        selected = selected_by_name.get(current)
        if selected:
            result.add(selected)
            continue
        dependency = raw_by_name.get(current)
        if dependency:
            stack.extend(values(dependency, "dependencies"))
    return sorted(result, key=natural_key)


def load_curated_manifest(project: Project) -> dict[str, Any] | None:
    path = project.root / "theorem-map.json"
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise GraphConfigError(f"invalid theorem-map manifest {path}: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("items"), list):
        raise GraphConfigError(f"invalid theorem-map manifest: {path}")
    return data


def merge_source_inventory(
    compiled_data: dict[str, Any], source_data: dict[str, Any]
) -> dict[str, Any]:
    """Overlay compiled dependency evidence on the complete source inventory.

    A project's aggregate root can omit labelled source files.  Compiled
    extraction remains authoritative for every item it sees, while the source
    pass keeps omitted literature items visible without inventing dependency
    edges for declarations Lean did not import.
    """

    compiled_project = compiled_data.get("project")
    source_project = source_data.get("project")
    if not isinstance(compiled_project, dict) or not isinstance(source_project, dict):
        raise GraphConfigError("source inventory merge requires project metadata")
    for field in ("id", "kind", "branch", "commit"):
        compiled_value = str(compiled_project.get(field) or "")
        source_value = str(source_project.get(field) or "")
        if compiled_value and source_value and compiled_value != source_value:
            raise GraphConfigError(
                f"source inventory project {field} mismatch: "
                f"{compiled_value!r} != {source_value!r}"
            )

    def unique_items(payload: dict[str, Any], label: str) -> list[dict[str, Any]]:
        raw_items = payload.get("items")
        if not isinstance(raw_items, list):
            raise GraphConfigError(f"{label} graph does not contain an item list")
        items: list[dict[str, Any]] = []
        seen: set[str] = set()
        for value in raw_items:
            if not isinstance(value, dict) or not value.get("id"):
                raise GraphConfigError(f"{label} graph contains an item without an id")
            item_id = str(value["id"])
            if item_id in seen:
                raise GraphConfigError(
                    f"{label} graph contains duplicate item id {item_id!r}"
                )
            seen.add(item_id)
            items.append(value)
        return items

    compiled_items = unique_items(compiled_data, "compiled")
    source_items = unique_items(source_data, "source inventory")
    compiled_by_id = {str(item["id"]): item for item in compiled_items}
    source_ids = {str(item["id"]) for item in source_items}
    merged_items: list[dict[str, Any]] = []
    source_only_count = 0
    for source_item in source_items:
        item_id = str(source_item["id"])
        compiled_item = compiled_by_id.pop(item_id, None)
        if compiled_item is not None:
            item = dict(compiled_item)
            item["dependencyEvidence"] = "compiled"
        else:
            item = dict(source_item)
            item["statementDependencies"] = []
            item["proofDependencies"] = []
            item["dependencies"] = []
            item["dependencyEvidence"] = "source-only"
            source_only_count += 1
        merged_items.append(item)
    for compiled_item in compiled_items:
        item_id = str(compiled_item["id"])
        if item_id not in compiled_by_id:
            continue
        item = dict(compiled_item)
        item["dependencyEvidence"] = "compiled"
        merged_items.append(item)

    merged_sections: list[dict[str, Any]] = []
    section_ids: set[str] = set()
    for payload in (source_data, compiled_data):
        sections = payload.get("sections")
        if not isinstance(sections, list):
            continue
        for section in sections:
            if not isinstance(section, dict) or not section.get("id"):
                continue
            section_id = str(section["id"])
            if section_id in section_ids:
                continue
            section_ids.add(section_id)
            merged_sections.append(dict(section))

    compiled_count = len(compiled_items)
    source_count = len(source_items)
    compiled_only_count = sum(
        str(item["id"]) not in source_ids for item in compiled_items
    )
    if not compiled_items and not source_items:
        dependency_coverage = "none"
    elif source_only_count == 0:
        dependency_coverage = "complete"
    elif compiled_count:
        dependency_coverage = "partial"
    else:
        dependency_coverage = "none"
    generation = dict(compiled_data.get("generation") or {})
    source_generation = source_data.get("generation")
    generation.update(
        {
            "inventoryMode": "source-plus-compiled",
            "compiledItemCount": compiled_count,
            "sourceInventoryItemCount": source_count,
            "sourceOnlyItemCount": source_only_count,
            "compiledOnlyItemCount": compiled_only_count,
            "mergedItemCount": len(merged_items),
            "dependencyCoverage": dependency_coverage,
        }
    )
    if isinstance(source_generation, dict):
        generation["sourceRawDeclarationCount"] = int(
            source_generation.get("rawDeclarationCount") or 0
        )

    merged = dict(compiled_data)
    merged["schemaVersion"] = 2
    merged["sections"] = merged_sections
    merged["items"] = merged_items
    merged["generation"] = generation
    return merged


def build_data(
    project: Project,
    raw_declarations: list[dict[str, Any]],
    repository: str,
    branch: str,
    commit: str,
    *,
    source_inventory_raw: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build the stable JSON payload consumed by the graph frontend."""

    curated = load_curated_manifest(project)
    if curated is not None:
        data = dict(curated)
        data.setdefault("schemaVersion", 1)
        project_data = dict(data.get("project") or {})
        project_data.update(
            {
                "id": project.project_id,
                "title": project_data.get("title") or project_title(project),
                "kind": project.kind,
                "branch": branch,
                "commit": commit,
                "repository": repository.rstrip("/"),
                "sourceRoot": project.source_root,
            }
        )
        data["project"] = project_data
        return data

    candidates = candidates_from_raw(project, raw_declarations)
    # This technical note uses named Lean results rather than numbered
    # literature labels. Keep the compiled declarations and their actual
    # dependency evidence; never invent a manuscript number or source edge.
    if not candidates and project.project_id == "RockafellarSum_2026" and project.root_module:
        for declaration in raw_declarations:
            doc = str(declaration.get("docString") or "").strip()
            name = str(declaration.get("name") or "")
            kind = str(declaration.get("kind") or "")
            if not doc or not name or name.startswith("_private.") or kind not in {"theorem", "lemma"}:
                continue
            module = str(declaration.get("moduleName") or "")
            relative = module_relative_file(project, module)
            section, section_label = section_for(relative, "")
            candidates.append(Candidate(
                label=name, item_id="declaration-" + name, item_type="Theorem" if kind == "theorem" else "Lemma",
                number="", title=clean_title_text(doc.split("\n\n", 1)[0]), statement=doc,
                declaration=name, declaration_kind=kind, module_name=module,
                relative_file=relative, line=int(declaration.get("line") or 1),
                section_id=section, section_label=section_label, score=0,
            ))
    selected = select_representatives(candidates)
    raw_by_name = {
        str(item.get("name")): item for item in raw_declarations if item.get("name")
    }
    selected_by_name = {item.declaration: item.item_id for item in selected}
    items: list[dict[str, Any]] = []
    for candidate in selected:
        dependencies = contract_dependencies(
            candidate.declaration, raw_by_name, selected_by_name
        )
        statement_dependencies = contract_dependencies(
            candidate.declaration,
            raw_by_name,
            selected_by_name,
            "statementDependencies",
        )
        proof_dependencies = contract_dependencies(
            candidate.declaration,
            raw_by_name,
            selected_by_name,
            "proofDependencies",
        )
        dependencies = [item for item in dependencies if item != candidate.item_id]
        statement_dependencies = [
            item for item in statement_dependencies if item != candidate.item_id
        ]
        proof_dependencies = [
            item for item in proof_dependencies if item != candidate.item_id
        ]
        items.append(
            {
                "id": candidate.item_id,
                "label": candidate.label,
                "title": candidate.title,
                "type": candidate.item_type,
                "section": candidate.section_id,
                "file": candidate.relative_file,
                "line": candidate.line,
                "declaration": candidate.declaration,
                "statement": candidate.statement,
                "statementDependencies": statement_dependencies,
                "proofDependencies": proof_dependencies,
                "dependencies": dependencies,
                "dependencyEvidence": (
                    "compiled" if project.root_module else "source-only"
                ),
            }
        )

    section_ids: list[str] = []
    section_labels: dict[str, str] = {}
    for candidate in selected:
        if candidate.section_id not in section_labels:
            section_ids.append(candidate.section_id)
            section_labels[candidate.section_id] = candidate.section_label
    sections = []
    for index, section_id in enumerate(section_ids):
        color, wash = PALETTE[index % len(PALETTE)]
        sections.append(
            {
                "id": section_id,
                "label": section_labels[section_id],
                "short": section_labels[section_id],
                "color": color,
                "wash": wash,
            }
        )

    data = {
        "schemaVersion": 2,
        "project": {
            "id": project.project_id,
            "title": project_title(project),
            "kind": project.kind,
            "branch": branch,
            "commit": commit,
            "repository": repository.rstrip("/"),
            "sourceRoot": project.source_root,
        },
        "sections": sections,
        "items": items,
        "generation": {
            "mode": "lean-environment" if project.root_module else "source-fallback",
            "rootModule": project.root_module or "",
            "rawDeclarationCount": len(raw_declarations),
            "dependencyModel": "statement-and-proof-v1",
        },
    }
    if project.root_module and source_inventory_raw is not None:
        source_data = build_data(
            replace(project, root_module=None),
            source_inventory_raw,
            repository=repository,
            branch=branch,
            commit=commit,
        )
        return merge_source_inventory(data, source_data)
    generation = data["generation"]
    if project.root_module:
        generation.update(
            {
                "inventoryMode": "compiled-only",
                "compiledItemCount": len(items),
                "sourceOnlyItemCount": 0,
                "mergedItemCount": len(items),
                "dependencyCoverage": "compiled-only",
            }
        )
    else:
        generation.update(
            {
                "inventoryMode": "source-only",
                "sourceInventoryItemCount": len(items),
                "sourceOnlyItemCount": len(items),
                "mergedItemCount": len(items),
                "dependencyCoverage": "none",
            }
        )
    return data


__all__ = [
    "CHAPTER_RE",
    "DECL_RE",
    "LABEL_RE",
    "Candidate",
    "PALETTE",
    "build_data",
    "candidate_score",
    "candidates_from_raw",
    "clean_title_text",
    "contract_dependencies",
    "fallback_raw_declarations",
    "load_curated_manifest",
    "merge_source_inventory",
    "module_relative_file",
    "natural_key",
    "normalize_label",
    "project_title",
    "section_for",
    "select_representatives",
    "slugify",
    "title_from_doc",
]
