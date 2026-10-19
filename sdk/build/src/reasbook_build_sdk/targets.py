"""Resolve ReasBook project names to stable Lake targets.

The repository has used two Lake layouts over time: an aggregate ``Books`` /
``Papers`` library and one library per project with ``srcDir`` pointing at one
of those directories. Keeping the small amount of layout knowledge here lets
deployment, documentation builds, and callers of the build SDK share one
deterministic rule.
"""

from __future__ import annotations

from pathlib import Path
import re
from typing import Any, Iterable

from .errors import ConfigurationError


LIBRARY_RE = re.compile(
    r"^[ \t]*lean_lib[ \t]+" r'(?:«([^»]+)»|"([^"]+)"|([^ \t]+))[ \t]+where\b'
)
SRC_DIR_RE = re.compile(r'^[ \t]*srcDir[ \t]*:=[ \t]*"([^"]+)"')
ROOTS_RE = re.compile(r"^[ \t]*roots[ \t]*:=[ \t]*#\[(.*)$")
ROOT_NAME_RE = re.compile(r"[`«\"]?([A-Za-z_][A-Za-z0-9_'.]*)[»\"]?")


def parse_library_declarations(lakefile: str | Path) -> dict[str, str | None]:
    """Return ``library name -> srcDir`` from a Lake Lean config file."""

    path = Path(lakefile).expanduser().resolve()
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError as exc:
        raise ConfigurationError(f"cannot read Lake file {path}: {exc}") from exc

    return parse_library_declarations_text("\n".join(lines))


def parse_library_declarations_text(text: str) -> dict[str, str | None]:
    """Parse ``lean_lib`` declarations from Lake source text."""

    declarations: dict[str, str | None] = {}
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = LIBRARY_RE.match(line.split("--", 1)[0])
        if not match:
            continue
        name = next(value for value in match.groups() if value is not None)
        src_dir: str | None = None
        cursor = index + 1
        while cursor < len(lines):
            candidate = lines[cursor]
            if candidate.strip() and not candidate[0].isspace():
                break
            src_match = SRC_DIR_RE.match(candidate.split("--", 1)[0])
            if src_match:
                src_dir = src_match.group(1).rstrip("/\\")
            cursor += 1
        declarations[name] = src_dir
    return declarations


def parse_library_roots_text(text: str) -> dict[str, tuple[str, ...]]:
    """Return explicit Lake ``roots`` for each ``lean_lib`` declaration."""

    roots: dict[str, tuple[str, ...]] = {}
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = LIBRARY_RE.match(line.split("--", 1)[0])
        if not match:
            continue
        name = next(value for value in match.groups() if value is not None)
        values: list[str] = []
        cursor = index + 1
        while cursor < len(lines):
            candidate = lines[cursor]
            if candidate.strip() and not candidate[0].isspace():
                break
            roots_match = ROOTS_RE.match(candidate.split("--", 1)[0])
            if roots_match:
                content = roots_match.group(1)
                while "]" not in content and cursor + 1 < len(lines):
                    cursor += 1
                    content += " " + lines[cursor].split("--", 1)[0].strip()
                content = content.split("]", 1)[0]
                values.extend(item for item in ROOT_NAME_RE.findall(content) if item)
            cursor += 1
        if values:
            roots[name] = tuple(dict.fromkeys(values))
    return roots


def target_from_declarations(
    declarations: dict[str, str | None],
    project: str,
    kind: str = "book",
    *,
    roots: dict[str, tuple[str, ...]] | None = None,
) -> str:
    """Resolve a root module without requiring a checked-out source tree."""

    kind_dir, leaf = _kind_parts(kind)
    if declarations.get(project) == kind_dir:
        if roots and roots.get(project):
            # An explicit root is the documentation/build entry point. The
            # library name may differ from that module (for example a project
            # library `DFP_wolfe_local` rooted at `DFP_wolfe_local.Paper`).
            return roots[project][0]
        return f"{project}.{leaf}"
    if kind_dir in declarations and declarations[kind_dir] is None:
        return f"{kind_dir}.{project}.{leaf}"
    if project in declarations:
        if roots and roots.get(project):
            return project
        return project
    raise ConfigurationError(f"{project} is not registered in the Lake declarations")


def _kind_parts(kind: str) -> tuple[str, str]:
    normalized = kind.strip().lower()
    if normalized in {"book", "books"}:
        return "Books", "Book"
    if normalized in {"paper", "papers"}:
        return "Papers", "Paper"
    raise ConfigurationError(f"kind must be book(s) or paper(s), got {kind!r}")


def _project_root(value: str | Path) -> Path:
    root = Path(value).expanduser().resolve()
    if not root.is_dir():
        raise ConfigurationError(f"Lake project directory does not exist: {root}")
    if (
        not (root / "lakefile.lean").is_file()
        and not (root / "lakefile.toml").is_file()
    ):
        raise ConfigurationError(f"missing Lake file under {root}")
    return root


def _aggregate_target(root: Path, kind_dir: str, project: str, leaf: str) -> str:
    source = root / kind_dir / project / f"{leaf}.lean"
    if not source.is_file():
        raise ConfigurationError(f"project source does not exist: {source}")
    return f"{kind_dir}.{project}.{leaf}"


def library_target(project_root: str | Path, project: str, kind: str = "book") -> str:
    """Resolve one project's root module target for ``kind``."""

    root = _project_root(project_root)
    kind_dir, leaf = _kind_parts(kind)
    declarations = parse_library_declarations(root / "lakefile.lean")
    roots = parse_library_roots_text(
        (root / "lakefile.lean").read_text(encoding="utf-8")
    )

    target = target_from_declarations(declarations, project, kind, roots=roots)
    if target == f"{kind_dir}.{project}.{leaf}":
        return _aggregate_target(root, kind_dir, project, leaf)
    return target


def project_doc_targets(
    project_root: str | Path, *, include_papers: bool = True
) -> list[str]:
    """List root ``:docs`` targets for registered projects."""

    root = _project_root(project_root)
    declarations = parse_library_declarations(root / "lakefile.lean")
    roots = parse_library_roots_text(
        (root / "lakefile.lean").read_text(encoding="utf-8")
    )
    kinds = (("Books", "Book"), ("Papers", "Paper"))
    if not include_papers:
        kinds = kinds[:1]

    targets: list[str] = []
    for kind_dir, leaf in kinds:
        aggregate = declarations.get(kind_dir) is None and kind_dir in declarations
        if aggregate:
            parent = root / kind_dir
            if parent.is_dir():
                targets.extend(
                    ".".join(path.relative_to(root).with_suffix("").parts)
                    for path in sorted(parent.glob(f"*/{leaf}.lean"))
                )
            continue
        targets.extend(
            name if roots.get(name) else f"{name}.{leaf}"
            for name, src_dir in sorted(declarations.items())
            if src_dir == kind_dir
        )
    return _unique(targets)


def selected_targets(
    project_root: str | Path,
    projects: Iterable[dict[str, Any]],
    *,
    include_docs: bool = True,
) -> list[str]:
    """Resolve target names from catalog records emitted by discovery."""

    root = _project_root(project_root)
    declarations = parse_library_declarations(root / "lakefile.lean")
    roots = parse_library_roots_text(
        (root / "lakefile.lean").read_text(encoding="utf-8")
    )
    targets: list[str] = []
    for project in projects:
        kind = project.get("kind")
        name = project.get("name")
        if not isinstance(kind, str) or not isinstance(name, str):
            continue
        try:
            kind_dir, leaf = _kind_parts(kind)
        except ConfigurationError:
            continue
        if declarations.get(name) == kind_dir:
            root_target = name if roots.get(name) else f"{name}.{leaf}"
        elif declarations.get(kind_dir) is None and kind_dir in declarations:
            root_target = f"{kind_dir}.{name}.{leaf}"
        else:
            continue
        if include_docs:
            targets.append(f"{root_target}:docs")
        targets.append(root_target)
    return _unique(targets)


def _unique(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


__all__ = [
    "LIBRARY_RE",
    "SRC_DIR_RE",
    "library_target",
    "parse_library_declarations",
    "parse_library_declarations_text",
    "project_doc_targets",
    "selected_targets",
    "target_from_declarations",
]
