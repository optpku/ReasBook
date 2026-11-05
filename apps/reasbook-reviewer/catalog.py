"""Catalog and manifest helpers for the ReasBook reviewer.

The catalog is intentionally small.  It describes where a project lives and
whether its review index has been built, but it does not contain declarations,
source text, or dependency graphs.  Those payloads are generated per book in a
later build stage.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Any, Iterable

import bootstrap  # noqa: F401
from reasbook_sdk_common import atomic_write_json
from settings import REPO_ROOT, cache_root

BOOK_SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,120}$")
SOURCE_LINK_RE = re.compile(
    r"Open the source on\s+`(?P<branch>[^`]+)`[^\n]*?"
    r"\((?P<url>https?://[^)\s]+)\)",
    re.IGNORECASE,
)
HEADING_RE = re.compile(r"^#\s+(?P<title>.+?)\s*$")


@dataclass(frozen=True)
class BookRecord:
    """One ReasBook project exposed by the reviewer."""

    slug: str
    title: str
    authors: str
    kind: str
    project_path: str
    source_available: bool
    branches: tuple[str, ...]
    source_urls: tuple[str, ...]
    review_index_state: str = "not-built"
    item_count: int = 0
    source_repository: str = "ReasBook"
    source_root: str = "ReasBook"
    module_prefix: str = ""
    toolchain: str | None = None
    review_source: str | None = None

    def as_dict(self) -> dict[str, Any]:
        artifact_root = f"data/books/{self.slug}"
        payload = {
            "slug": self.slug,
            "title": self.title,
            "authors": self.authors,
            "kind": self.kind,
            "projectPath": self.project_path,
            "sourceAvailable": self.source_available,
            "branches": list(self.branches),
            "sourceUrls": list(self.source_urls),
            "reviewIndex": {
                "state": self.review_index_state,
                "itemCount": self.item_count,
                "path": f"{artifact_root}/index.json",
            },
            "artifacts": {
                "index": {"state": self.review_index_state, "path": f"{artifact_root}/index.json"},
                "source": {"state": "not-built", "path": f"{artifact_root}/source.json"},
                "docs": {"state": "not-built", "path": f"{artifact_root}/docs.json"},
                "graphs": {"state": "not-built", "path": f"{artifact_root}/graphs.json"},
            },
        }
        if self.source_repository != "ReasBook":
            payload["sourceRepository"] = self.source_repository
        if self.source_root != "ReasBook":
            payload["sourceRoot"] = self.source_root
        if self.module_prefix:
            payload["modulePrefix"] = self.module_prefix
        if self.toolchain:
            payload["toolchain"] = self.toolchain
        if self.review_source:
            payload["reviewSource"] = self.review_source
        return payload


class CatalogError(ValueError):
    """Raised when a catalog file cannot be used safely."""


def default_reasbook_root() -> Path:
    """Resolve the owning ReasBook checkout, honoring an explicit override."""

    configured = os.environ.get("REASBOOK_ROOT", "").strip()
    if configured:
        return Path(configured).expanduser().resolve()
    return REPO_ROOT


def _split_heading(title: str) -> tuple[str, str]:
    # ReasBook catalog headings use ``Title - Author (year)``.  Keep the full
    # heading available as the title when a future entry does not follow that
    # convention.
    separator = next((value for value in (" - ", " — ") if value in title), None)
    if separator is None:
        return title.strip(), ""
    name, authors = title.split(separator, 1)
    return name.strip(), authors.strip()


def _read_project_metadata(readme: Path) -> tuple[str, str, tuple[str, ...], tuple[str, ...], bool]:
    text = readme.read_text(encoding="utf-8", errors="replace")
    heading = next(
        (match.group("title") for line in text.splitlines() if (match := HEADING_RE.match(line))),
        readme.parent.name,
    )
    title, authors = _split_heading(heading)
    # Main's bilingual catalog carries original-reference authors separately
    # from the formalization roster. Some short project landing pages omit
    # those bibliographic fields, so use the owning catalog's exact project row.
    if len(readme.parents) > 3:
        root = readme.parents[3]
        catalog = root / "README.md"
        project_path = readme.parent.relative_to(root).as_posix()
        if catalog.is_file():
            for line in catalog.read_text(encoding="utf-8").splitlines():
                match = re.match(r"\| \*\*\[([^]]+)\]\((?:\./)?" + re.escape(project_path)
                                 + r"/\)\*\*<br><sub>(.*?)</sub>", line)
                if match:
                    title = match[1].strip()
                    if not authors and re.search(r"[A-Za-z]", match[2]):
                        authors = re.sub(r"<[^>]+>", "", match[2]).strip()
                    break
    if not authors:
        match = re.search(r"^-\s+\*\*Authors?:\*\*\s*(.+)$", text, re.MULTILINE)
        if match:
            authors = match[1].strip()
    branches: list[str] = []
    urls: list[str] = []
    for match in SOURCE_LINK_RE.finditer(text):
        branch = match.group("branch").strip()
        if branch and branch not in branches:
            branches.append(branch)
        # Keep the original URL instead of reconstructing it: catalog links can
        # point at a fork or a branch with a non-standard name.
        url = match.group("url")
        if not url.startswith(("http://", "https://")):
            kind_dir = readme.parent.parent.name
            url = f"https://github.com/optpku/ReasBook/tree/{branch}/ReasBook/{kind_dir}/{readme.parent.name}/"
        if url not in urls:
            urls.append(url)
    source_available = bool(branches) and "Source: TBD" not in text
    return title, authors, tuple(branches), tuple(urls), source_available


def _source_exists_in_git(repo_root: Path, branch: str, project_path: str) -> bool | None:
    """Return whether a source file exists in a local ref, or ``None`` if unknown."""

    if not branch:
        return None
    # The working tree usually contains only the catalog branch.  Looking at a
    # local origin ref avoids checking out every large version branch just to
    # populate the small catalog.  Missing git/ref information is not an error.
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "ls-tree", "-r", "--name-only", f"origin/{branch}", project_path],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    leaf = Path(project_path).name
    return any(Path(line.strip()).name == leaf for line in result.stdout.splitlines())


def _iter_project_dirs(reasbook_root: Path, kind: str) -> Iterable[Path]:
    root = reasbook_root / "ReasBook" / kind
    if not root.is_dir():
        return ()
    return sorted((path for path in root.iterdir() if path.is_dir() and (path / "README.md").is_file()), key=lambda path: path.name.lower())


def discover_books(reasbook_root: Path | None = None, *, include_papers: bool = False) -> list[BookRecord]:
    """Discover catalog entries without building any review payloads."""

    root = (reasbook_root or default_reasbook_root()).resolve()
    kinds = [("Books", "book")]
    if include_papers:
        kinds.append(("Papers", "paper"))
    records: list[BookRecord] = []
    seen_slugs: set[str] = set()
    for directory_name, kind in kinds:
        for project_dir in _iter_project_dirs(root, directory_name):
            slug = project_dir.name.lower()
            if not BOOK_SLUG_RE.fullmatch(slug):
                # A source directory name is part of the public URL.  Refuse
                # ambiguous names instead of silently creating an unsafe route.
                continue
            if slug in seen_slugs:
                raise CatalogError(f"book slug collision after normalization: {slug}")
            seen_slugs.add(slug)
            title, authors, branches, urls, available = _read_project_metadata(project_dir / "README.md")
            project_path = f"ReasBook/{directory_name}/{project_dir.name}"
            source_leaf = "Book.lean" if kind == "book" else "Paper.lean"
            if available and branches:
                known = [_source_exists_in_git(root, branch, f"{project_path}/{source_leaf}") for branch in branches]
                if known and all(value is False for value in known):
                    available = False
            records.append(
                BookRecord(
                    slug=slug,
                    title=title,
                    authors=authors,
                    kind=kind,
                    project_path=project_path,
                    source_available=available,
                    branches=branches,
                    source_urls=urls,
                )
            )
    return records


def discover_stacks_project(stacks_root: Path | None = None) -> BookRecord | None:
    """Return a catalog record for the sibling Stacks Lean project.

    The Stacks checkout is intentionally treated as one logical book. Its
    chapter/declaration index is generated separately, so discovering it never
    invokes Lake or copies the large source tree into the reviewer.
    """

    configured = os.environ.get("REASBOOK_STACKS_ROOT", "").strip()
    root = (
        stacks_root
        or (Path(configured).expanduser() if configured else None)
        or default_reasbook_root().parent / "Review" / "stacks-proof-module-migration"
    ).resolve()
    project_root = root / "stacks_project"
    if not project_root.is_dir():
        return None
    toolchain = None
    toolchain_path = root / "lean-toolchain"
    if toolchain_path.is_file():
        toolchain = toolchain_path.read_text(encoding="utf-8", errors="replace").strip() or None
    branch = toolchain.split(":", 1)[-1] if toolchain and ":" in toolchain else (toolchain or "")
    source_url = "https://stacks.math.columbia.edu/"
    prepared_pr = (cache_root() / "pr" / "stacks-project-v4.30.0").resolve()
    prepared_books = prepared_pr / "ReasBook" / "Books"
    # The PR helper permits a caller-supplied, schema-valid project ID.  Detect
    # the prepared source by shape instead of coupling the catalog to one ID.
    review_source = (
        "cache/reasbook/pr/stacks-project-v4.30.0"
        if any(path.is_dir() and path.name.startswith("StacksProject_") for path in prepared_books.glob("StacksProject_*"))
        else None
    )
    return BookRecord(
        slug="stacks_project",
        title="The Stacks Project",
        authors="The Stacks Project contributors",
        kind="book",
        project_path="Review/stacks-proof-module-migration/stacks_project",
        source_available=True,
        branches=(branch,) if branch else (),
        source_urls=(source_url,),
        source_repository="Review",
        source_root="Review/stacks-proof-module-migration",
        module_prefix="stacks_project",
        toolchain=toolchain,
        review_source=review_source,
    )


def catalog_payload(
    records: Iterable[BookRecord],
    *,
    reasbook_root: Path | None = None,
    extra_sources: Iterable[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    entries = [record.as_dict() for record in records]
    payload: dict[str, Any] = {
        "schemaVersion": 1,
        "generatedAt": None,
        "source": {
            "repository": "ReasBook",
            # Public catalog identity must not disclose a local checkout name.
            "root": "ReasBook",
        },
        "cachePolicy": {
            "mode": "on-demand",
            "generated": False,
            "description": "Statement indexes are generated per book; release source, docs, Verso, and graph evidence is resolved read-only when available.",
        },
        "books": entries,
    }
    sources = list(extra_sources or [])
    if sources:
        payload["source"]["additional"] = sources
    return payload


def load_catalog(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CatalogError(f"cannot read catalog {path}: {exc}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("books"), list):
        raise CatalogError("catalog must contain a books array")
    seen: set[str] = set()
    for entry in payload["books"]:
        if not isinstance(entry, dict):
            raise CatalogError("catalog book entries must be objects")
        slug = entry.get("slug")
        if not isinstance(slug, str) or not BOOK_SLUG_RE.fullmatch(slug) or slug in seen:
            raise CatalogError(f"invalid or duplicate book slug: {slug!r}")
        seen.add(slug)
    return payload


def write_catalog(path: Path, payload: dict[str, Any]) -> None:
    """Atomically publish a catalog so a running server never reads half JSON."""

    published = atomic_write_json(Path(path).expanduser().resolve(), payload)
    published.chmod(0o644)
