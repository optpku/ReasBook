"""Deterministic target artifacts derived from one verified release site."""

from __future__ import annotations

from dataclasses import replace
import hashlib
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
from urllib.parse import unquote, urljoin, urlsplit
import uuid

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployExecutionError
from ..git import version_key
from .models import (
    GITHUB_PAGES_HARD_SITE_BYTES,
    ReleaseArtifactPolicy,
    ReleaseSpec,
)
from .results import (
    BundleInfo,
    ReleaseArtifactRecord,
    ReleaseManifest,
    ReleaseSetManifest,
)
from .store import ReleaseLayout, ReleaseStore
from .static_assets import deduplicate_verso_assets


_SHARED_DOC_DIRECTORIES = {"declarations", "find", "src"}
README_URL = "https://github.com/optpku/ReasBook#readme"
_EXTERNAL_DOC_NAMESPACES = {
    "Aesop",
    "Batteries",
    "Cli",
    "ImportGraph",
    "Init",
    "Lake",
    "Lean",
    "Mathlib",
    "Plausible",
    "Qq",
    "Std",
}
_PAGES_ROOT_FILES = {
    ".nojekyll",
    "-verso-docs.json",
    "404.html",
    "index.html",
    "release-spec.json",
    "tooling-snapshot.json",
    "unavailable-documentation.json",
}


class _ReferenceParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.base_href: str | None = None
        self.references: list[tuple[str, str, str]] = []

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        values = dict(attrs)
        if tag == "base":
            if self.base_href is None and values.get("href"):
                self.base_href = values["href"]
            return
        if (
            tag == "meta"
            and (values.get("http-equiv") or "").lower() == "refresh"
            and values.get("content")
        ):
            match = re.match(
                r"^\s*\d+(?:\.\d+)?\s*;\s*url\s*=\s*(.*?)\s*$",
                values["content"],
                flags=re.IGNORECASE,
            )
            if match and match.group(1):
                self.references.append((tag, "refresh", match.group(1).strip("\"'")))
        for attribute in ("href", "src"):
            value = values.get(attribute)
            if value:
                self.references.append((tag, attribute, value))


def artifact_policy_digest(
    policies: tuple[ReleaseArtifactPolicy, ...],
) -> str:
    payload = {
        policy.name: policy.public_dict()
        for policy in sorted(policies, key=lambda item: item.name)
    }
    encoded = json.dumps(
        payload,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


class PagesSiteProjector:
    """Create a bounded Pages view without changing the full release tree.

    Canonical project pages retain their original version-qualified URLs.
    Every API page owned by a selected project remains byte-identical. External
    dependency pages reached by those documents become explicit lightweight
    placeholders; referenced styles, scripts, images, and search data remain
    byte-identical.
    """

    def __init__(self, *, max_site_bytes: int | None = None) -> None:
        if max_site_bytes is not None and (
            isinstance(max_site_bytes, bool) or max_site_bytes < 1
        ):
            raise ValueError("max_site_bytes must be a positive integer")
        self.max_site_bytes = max_site_bytes

    def project(
        self,
        spec: ReleaseSpec,
        source: Path,
        destination: Path,
    ) -> Path:
        full_site = Path(source).expanduser().resolve()
        target = Path(destination).expanduser().resolve(strict=False)
        self._validate_site(full_site)
        if (
            full_site == target
            or full_site in target.parents
            or target in full_site.parents
        ):
            raise DeployExecutionError(
                "Pages artifact and full site must be disjoint trees"
            )

        target.parent.mkdir(parents=True, exist_ok=True)
        staged = target.parent / f".pages-site-{uuid.uuid4().hex}"
        backup = target.parent / f".pages-site-backup-{uuid.uuid4().hex}"
        try:
            staged.mkdir()
            self._copy_catalog_shell(spec, full_site, staged)
            atomic_write_json(staged / "release-spec.json", spec.public_dict())
            versions = staged / "versions"
            versions.mkdir()
            canonical_routes: dict[str, tuple[Path | None, Path | None]] = {}
            for branch in sorted(
                spec.branches,
                key=lambda item: version_key(item.name),
            ):
                canonical_routes.update(
                    self._project_branch(spec, full_site, versions, branch.name)
                )
            self._copy_if_present(
                full_site,
                staged,
                Path("versions") / "index.html",
            )
            self._write_catalog_redirects(spec, staged, canonical_routes)
            self._write_historical_reading_redirects(spec, full_site, staged, canonical_routes)
            deduplicate_verso_assets(staged, spec.base_path)
            self._close_internal_references(
                spec,
                full_site,
                staged,
                canonical_routes,
            )
            self._validate_required_content(spec, staged, canonical_routes)
            self._validate_site(staged)
            total_bytes = sum(
                path.stat().st_size for path in staged.rglob("*") if path.is_file()
            )
            self._validate_capacity(total_bytes)
            self._publish(staged, target, backup)
            return target
        finally:
            if staged.exists():
                shutil.rmtree(staged)
            if backup.exists() or backup.is_symlink():
                if backup.is_dir() and not backup.is_symlink():
                    shutil.rmtree(backup)
                else:
                    backup.unlink(missing_ok=True)

    def _copy_catalog_shell(
        self,
        spec: ReleaseSpec,
        source: Path,
        destination: Path,
    ) -> None:
        """Copy only host-neutral catalog content into the Pages projection.

        The aggregate site also contains unversioned copies of every Verso
        route.  Copying that tree and deleting selected paths afterwards is
        both expensive and easy to get wrong, so Pages starts from an empty
        directory and admits only its public shell and canonical entrypoints.
        """

        for name in sorted(_PAGES_ROOT_FILES):
            self._copy_if_present(source, destination, Path(name))
        for relative in (Path("static"), Path("docs")):
            self._copy_if_present(source, destination, relative)
        self._copy_if_present(
            source,
            destination,
            Path("theorem-maps") / "index.html",
        )

        sites = source / "sites"
        if sites.is_dir():
            for child in sorted(sites.iterdir(), key=lambda item: item.name):
                if child.is_file():
                    self._copy_if_present(
                        source,
                        destination,
                        child.relative_to(source),
                    )
        for project in spec.canonical_projects():
            self._copy_if_present(
                source,
                destination,
                Path("sites") / project.slug / "index.html",
            )
            self._copy_if_present(
                source,
                destination,
                Path("theorem-maps") / project.kind / project.slug,
            )

    def _project_branch(
        self,
        spec: ReleaseSpec,
        full_site: Path,
        versions: Path,
        branch: str,
    ) -> dict[str, tuple[Path | None, Path | None]]:
        source = full_site / "versions" / branch
        if not source.is_dir():
            raise DeployExecutionError(
                f"full release is missing version tree required by Pages: {branch}"
            )
        target = versions / branch
        target.mkdir()
        branch_projects = tuple(
            project for project in spec.projects if project.branch == branch
        )
        projects = tuple(
            project for project in branch_projects if project.canonical
        )

        for relative in (Path("static"), Path("-verso-docs.json")):
            self._copy_if_present(source, target, relative)
        self._copy_doc_runtime(source, target, spec.base_path)

        # Documentation ownership is recorded for every ProjectSpec, not only
        # the projects selected as catalog canonicals. Copy all known project
        # namespaces before link closure so cross-project API links remain real.
        project_docs: dict[str, Path] = {}
        # A retained doc-gen navbar/search database can name an older namespace
        # of a selected project. Keep its real API pages even when that reading
        # occurrence is no longer selected; never replace them with fake stubs.
        documentation_owners = {project.key: project for project in spec.projects}
        for project in documentation_owners.values():
            if "docs" not in project.outputs:
                continue
            docs = self._copy_project_docs(
                source,
                target,
                project.kind,
                project.project_id,
                project.build_target,
            )
            if docs is None:
                if project.key not in {item.key for item in branch_projects}:
                    continue
                raise DeployExecutionError(
                    "Pages projection has no project-owned API entry: "
                    f"{project.key}@{branch}"
                )
            project_docs[project.key] = docs

        project_routes: list[tuple[str, str]] = []
        canonical_routes: dict[str, tuple[Path | None, Path | None]] = {}
        for project in projects:
            candidates = (
                Path(project.kind) / project.slug,
                Path(project.slug),
            )
            chosen: Path | None = None
            chosen_score = (-1, -1, -1)
            for relative in candidates:
                if self._copy_if_present(source, target, relative):
                    score = self._verso_route_score(source / relative)
                    if score > chosen_score:
                        chosen = relative
                        chosen_score = score
            self._copy_if_present(
                source,
                target,
                Path("theorem-maps") / project.kind / project.slug,
            )
            docs = project_docs.get(project.key)
            if "docs" in project.outputs and docs is None:
                raise DeployExecutionError(
                    f"Pages projection has no canonical API entry: {project.key}"
                )
            if chosen is not None:
                project_routes.append(
                    (
                        chosen.as_posix().rstrip("/") + "/",
                        project.project_id,
                    )
                )
            canonical_routes[project.key] = (
                Path("versions") / branch / chosen if chosen is not None else None,
                Path("versions") / branch / docs if docs is not None else None,
            )

        (target / "index.html").write_text(
            self._branch_index(branch, project_routes),
            encoding="utf-8",
        )
        return canonical_routes

    @staticmethod
    def _verso_route_score(root: Path) -> tuple[int, int, int]:
        """Prefer a directly serveable landing before a larger route fragment.

        Recent branch sites split the landing page under ``books|papers/slug``
        from a usually much larger legacy ``slug`` tree.  The latter often has
        chapter pages but no root ``index.html``; GitHub Pages cannot serve it
        as the target of the catalog redirect.  Both trees are retained for
        their internal URLs, but only an indexed tree may win over one without
        a landing page.
        """

        html_files = tuple(
            path
            for path in root.rglob("*.html")
            if path.is_file() and path.stat().st_size > 0
        )
        index = root / "index.html"
        has_valid_index = int(index.is_file() and index.stat().st_size > 0)
        return (
            has_valid_index,
            sum(path.stat().st_size for path in html_files),
            len(html_files),
        )

    @staticmethod
    def _copy_if_present(source: Path, destination: Path, relative: Path) -> bool:
        item = source / relative
        if item.is_symlink():
            raise DeployExecutionError(f"release site contains a symlink: {item}")
        if item.is_dir():
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(item, target, dirs_exist_ok=True)
            return True
        if item.is_file():
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(item, target)
            return True
        return False

    def _copy_doc_runtime(
        self,
        source: Path,
        destination: Path,
        base_path: str,
    ) -> None:
        docs = source / "docs"
        if not docs.is_dir():
            return
        target_docs = destination / "docs"
        target_docs.mkdir(parents=True, exist_ok=True)
        for child in docs.iterdir():
            if child.is_file():
                self._copy_doc_runtime_file(
                    source,
                    destination,
                    child,
                    base_path,
                )

        for root_name in ("ReasBook",):
            root = docs / root_name
            if not root.is_dir():
                continue
            target_root = target_docs / root_name
            target_root.mkdir(parents=True, exist_ok=True)
            for child in root.iterdir():
                relative = child.relative_to(source)
                if child.is_file():
                    self._copy_doc_runtime_file(
                        source,
                        destination,
                        child,
                        base_path,
                    )
                elif child.name in _SHARED_DOC_DIRECTORIES:
                    self._copy_if_present(source, destination, relative)

    def _copy_doc_runtime_file(
        self,
        source: Path,
        destination: Path,
        item: Path,
        base_path: str,
    ) -> None:
        relative = item.relative_to(source)
        if item.is_symlink():
            raise DeployExecutionError(f"release site contains a symlink: {item}")
        if self._is_external_root_api_doc(item):
            self._write_api_stub(destination / relative, base_path)
            return
        self._copy_if_present(source, destination, relative)

    @staticmethod
    def _is_external_root_api_doc(source: Path) -> bool:
        if source.suffix.lower() not in {".html", ".htm"}:
            return False
        if source.stem in _EXTERNAL_DOC_NAMESPACES:
            return True
        return 'data-reasbook-doc-stub="true"' in source.read_text(
            encoding="utf-8",
            errors="replace",
        )

    def _copy_project_docs(
        self,
        source: Path,
        destination: Path,
        kind: str,
        project_id: str,
        build_target: str,
    ) -> Path | None:
        kind_title = "Books" if kind == "books" else "Papers"
        candidates = (
            Path("docs") / "ReasBook" / kind_title / project_id,
            Path("docs") / "ReasBook" / project_id,
            Path("docs") / kind_title / project_id,
            Path("docs") / project_id,
            Path("docs") / "ReasBook" / f"{project_id}.html",
            Path("docs") / f"{project_id}.html",
        )
        entry_names = tuple(
            dict.fromkeys(
                (
                    build_target.rsplit(".", 1)[-1],
                    "Book" if kind == "books" else "Paper",
                    "Main",
                )
            )
        )
        entry_candidates: list[Path] = []
        for relative in candidates:
            item = source / relative
            if item.is_dir():
                for name in entry_names:
                    entry = relative / f"{name}.html"
                    if (source / entry).is_file():
                        entry_candidates.append(entry)
                        break
            elif item.is_file():
                entry_candidates.append(relative)
        if not entry_candidates:
            return None

        # A project may have both a top-level module HTML file and a sibling
        # namespace directory (for example an explicit Lake root). Once an
        # entry establishes ownership, retain every ProjectSpec-derived shape.
        for relative in candidates:
            self._copy_if_present(source, destination, relative)
        return entry_candidates[0]

    def _validate_capacity(self, total_bytes: int) -> None:
        """Apply GitHub's hard limit independently of the profile safety line."""

        if total_bytes > GITHUB_PAGES_HARD_SITE_BYTES:
            raise DeployExecutionError(
                f"Pages projection is {total_bytes} bytes; GitHub Pages hard "
                f"limit is {GITHUB_PAGES_HARD_SITE_BYTES}"
            )
        if self.max_site_bytes is not None and total_bytes > self.max_site_bytes:
            raise DeployExecutionError(
                f"Pages projection is {total_bytes} bytes; budget is "
                f"{self.max_site_bytes}"
            )

    def _write_historical_reading_redirects(
        self, spec: ReleaseSpec, source: Path, target: Path,
        routes: dict[str, tuple[Path | None, Path | None]],
    ) -> None:
        # Sidebar URLs live in JavaScript, so ordinary HTML link closure does
        # not discover every historical route. Keep all known reading indexes
        # as tiny explicit redirects, never copy their old proof bodies.
        for branch in spec.branches:
            for project in spec.canonical_projects():
                if project.branch == branch.name:
                    continue
                for root in (Path(project.kind) / project.slug, Path(project.slug)):
                    relative = Path("versions") / branch.name / root
                    for index in (source / relative).rglob("index.html"):
                        route = index.relative_to(source)
                        destination = target / route
                        if destination.exists():
                            continue
                        canonical = self._canonical_history_target(spec, route, target, routes)
                        if canonical is not None:
                            self._write_history_redirect(destination, canonical, spec.base_path)

    def _write_catalog_redirects(
        self,
        spec: ReleaseSpec,
        site: Path,
        routes: dict[str, tuple[Path | None, Path | None]],
    ) -> None:
        for project in spec.canonical_projects():
            route = routes.get(project.key)
            if route is None:
                raise DeployExecutionError(f"Pages projection omitted {project.key}")
            pages, docs = route
            if pages is not None:
                self._write_redirect(
                    site / "sites" / project.slug / "pages" / "index.html",
                    spec.base_path + pages.as_posix().rstrip("/") + "/",
                    f"{project.project_id} pages",
                    spec.base_path,
                )
            if docs is not None:
                self._write_redirect(
                    site / "sites" / project.slug / "docs" / "index.html",
                    spec.base_path + docs.as_posix(),
                    f"{project.project_id} documentation",
                    spec.base_path,
                )

    @staticmethod
    def _write_redirect(
        path: Path,
        target: str,
        title: str,
        base_path: str,
    ) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        escaped_target = html.escape(target, quote=True)
        escaped_title = html.escape(title)
        stylesheet = html.escape(base_path + "static/catalog.css", quote=True)
        path.write_text(
            "\n".join(
                [
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" '
                    'content="width=device-width,initial-scale=1" />',
                    f'  <meta http-equiv="refresh" content="0; url={escaped_target}" />',
                    f"  <title>{escaped_title}</title>",
                    f'  <link rel="stylesheet" href="{stylesheet}" />',
                    "</head>",
                    '<body class="redirect-page">',
                    f'  <p><a href="{escaped_target}">Open {escaped_title}</a></p>',
                    "</body>",
                    "</html>",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _branch_index(
        branch: str,
        routes: list[tuple[str, str]],
    ) -> str:
        # Version roots are compatibility entrypoints, not another catalog.
        # Project routes below them remain intact for Docs/Verso deep links.
        target = README_URL
        return "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                '  <meta name="robots" content="noindex,follow" />',
                f'  <meta http-equiv="refresh" content="0; url={target}" />',
                f'  <link rel="canonical" href="{target}" />',
                "  <title>ReasBook README</title>",
                "</head>",
                "<body>",
                f'  <p><a href="{target}">Open ReasBook README</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        )

    def _close_internal_references(
        self,
        spec: ReleaseSpec,
        full_site: Path,
        pages_site: Path,
        canonical_routes: dict[str, tuple[Path | None, Path | None]],
    ) -> None:
        origin = "https://reasbook.invalid"
        base_path = spec.base_path
        errors: list[str] = []
        documents = sorted(pages_site.rglob("*.html"))
        for document in documents:
            parser = _ReferenceParser()
            parser.feed(document.read_text(encoding="utf-8", errors="replace"))
            relative_document = document.relative_to(pages_site).as_posix()
            document_url = origin + base_path + relative_document
            document_base = (
                urljoin(document_url, parser.base_href)
                if parser.base_href
                else document_url
            )
            for tag, attribute, value in parser.references:
                missing = self._resolve_missing_reference(
                    origin,
                    base_path,
                    document_base,
                    value,
                    pages_site,
                )
                if missing is None:
                    continue
                relative, target = missing
                source = full_site / relative
                if source.is_file():
                    if source.suffix.lower() in {".html", ".htm"}:
                        if self._is_external_api_doc(relative, source):
                            self._write_api_stub(target, spec.base_path)
                        elif history_target := self._canonical_history_target(
                            spec,
                            relative,
                            pages_site,
                            canonical_routes,
                        ):
                            self._write_history_redirect(
                                target,
                                history_target,
                                spec.base_path,
                            )
                        else:
                            errors.append(
                                f"{relative_document}: omitted non-dependency "
                                f"page {value}"
                            )
                    else:
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(source, target)
                elif source.is_dir() and (source / "index.html").is_file():
                    if self._is_external_api_doc(
                        relative / "index.html",
                        source / "index.html",
                    ):
                        self._write_api_stub(
                            target / "index.html",
                            spec.base_path,
                        )
                    elif history_target := self._canonical_history_target(
                        spec,
                        relative / "index.html",
                        pages_site,
                        canonical_routes,
                    ):
                        self._write_history_redirect(
                            target / "index.html",
                            history_target,
                            spec.base_path,
                        )
                    else:
                        errors.append(
                            f"{relative_document}: omitted non-dependency directory {value}"
                        )
                else:
                    errors.append(
                        f"{relative_document}: {tag}.{attribute} target is missing: {value}"
                    )
        if errors:
            preview = "; ".join(errors[:20])
            suffix = f"; and {len(errors) - 20} more" if len(errors) > 20 else ""
            raise DeployExecutionError(
                f"Pages projection has broken links: {preview}{suffix}"
            )

    @staticmethod
    def _resolve_missing_reference(
        origin: str,
        base_path: str,
        document_base: str,
        value: str,
        pages_site: Path,
    ) -> tuple[Path, Path] | None:
        reference = value.strip()
        if not reference or reference.startswith(
            ("#", "data:", "javascript:", "mailto:")
        ):
            return None
        resolved = urlsplit(urljoin(document_base, reference))
        if (
            resolved.scheme not in {"http", "https"}
            or resolved.netloc != "reasbook.invalid"
        ):
            return None
        path = unquote(resolved.path)
        root_request = path.rstrip("/") == base_path.rstrip("/")
        if root_request:
            relative = Path("index.html")
        elif path.startswith(base_path):
            relative_text = path[len(base_path) :].lstrip("/")
            relative_url = PurePosixPath(relative_text or "index.html")
            if (
                relative_url.is_absolute()
                or any(part in {"", ".", ".."} for part in relative_url.parts)
                or "\\" in relative_text
                or "\x00" in relative_text
            ):
                raise DeployExecutionError(
                    f"Pages link has an unsafe internal path: {value}"
                )
            relative = Path(*relative_url.parts)
        else:
            raise DeployExecutionError(
                f"Pages link escapes configured base path {base_path}: {value}"
            )
        target = pages_site / relative
        if pages_site not in target.resolve(strict=False).parents:
            raise DeployExecutionError(
                f"Pages link escapes the projected site: {value}"
            )
        if (path.endswith("/") and not root_request) or target.is_dir():
            target = target / "index.html"
            relative = relative / "index.html"
        if target.is_file():
            return None
        return relative, target

    @staticmethod
    def _is_omitted_api_doc(relative: Path) -> bool:
        parts = relative.parts
        return len(parts) >= 4 and parts[0] == "versions" and parts[2] == "docs"

    @classmethod
    def _is_external_api_doc(cls, relative: Path, source: Path) -> bool:
        """Recognize dependency docs without silently reclassifying project pages."""

        if not cls._is_omitted_api_doc(relative):
            return False
        if source.is_file() and 'data-reasbook-doc-stub="true"' in source.read_text(
            encoding="utf-8",
            errors="replace",
        ):
            return True
        tail = relative.parts[3:]
        if tail and tail[0] == "ReasBook":
            tail = tail[1:]
        if not tail:
            return False
        return Path(tail[0]).stem in _EXTERNAL_DOC_NAMESPACES

    @staticmethod
    def _canonical_history_target(
        spec: ReleaseSpec,
        relative: Path,
        pages_site: Path,
        canonical_routes: dict[str, tuple[Path | None, Path | None]],
    ) -> str | None:
        parts = relative.parts
        if len(parts) < 4 or parts[0] != "versions":
            return None
        branch = parts[1]
        route = Path(*parts[2:])
        for project in spec.projects:
            # Canonical-only releases deliberately omit old ProjectSpecs, but
            # old, verified API pages can still link to their Verso URLs.
            if project.canonical and project.branch == branch:
                continue
            if not project.canonical and project.branch != branch:
                continue
            for root in (Path(project.kind) / project.slug, Path(project.slug)):
                if route == root or root in route.parents:
                    canonical = next(
                        (
                            candidate
                            for candidate in spec.projects
                            if candidate.key == project.key and candidate.canonical
                        ),
                        None,
                    )
                    if canonical is None:
                        return None
                    canonical_route = canonical_routes.get(canonical.key)
                    if canonical_route is None or canonical_route[0] is None:
                        return None
                    canonical_root = canonical_route[0]
                    canonical_index = pages_site / canonical_root / "index.html"
                    if not canonical_index.is_file():
                        return None

                    # Preserve a deep route when the canonical version exposes
                    # the same suffix. Otherwise land on its verified root.
                    suffix = route.relative_to(root)
                    candidate = pages_site / canonical_root / suffix
                    if candidate.is_file():
                        route_target = canonical_root / suffix
                        if route_target.name == "index.html":
                            return (
                                spec.base_path
                                + route_target.parent.as_posix().rstrip("/")
                                + "/"
                            )
                        return spec.base_path + route_target.as_posix()
                    return spec.base_path + canonical_root.as_posix().rstrip("/") + "/"
        return None

    @staticmethod
    def _write_api_stub(path: Path, base_path: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        home = html.escape(base_path, quote=True)
        path.write_text(
            "\n".join(
                [
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" '
                    'content="width=device-width,initial-scale=1" />',
                    "  <title>External dependency documentation</title>",
                    f'  <link rel="stylesheet" href="{home}static/catalog.css" />',
                    "</head>",
                    '<body data-reasbook-doc-stub="true">',
                    '  <main class="page-shell narrow-shell">',
                    '    <p class="eyebrow">Canonical Pages Projection</p>',
                    "    <h1>External dependency documentation</h1>",
                    "    <p>This external API page is outside the project-owned "
                    "documentation retained by GitHub Pages. Project API pages "
                    "remain available in full.</p>",
                    f'    <p><a class="back-link" href="{home}">'
                    "Back to ReasBook</a></p>",
                    "  </main>",
                    "</body>",
                    "</html>",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _write_history_redirect(
        path: Path,
        target: str,
        base_path: str,
    ) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        home = html.escape(base_path, quote=True)
        escaped_target = html.escape(target, quote=True)
        path.write_text(
            "\n".join(
                [
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" '
                    'content="width=device-width,initial-scale=1" />',
                    f'  <meta http-equiv="refresh" content="0; url={escaped_target}" />',
                    f'  <link rel="canonical" href="{escaped_target}" />',
                    "  <title>Canonical project version</title>",
                    f'  <link rel="stylesheet" href="{home}static/catalog.css" />',
                    "</head>",
                    '<body data-reasbook-history-redirect="true">',
                    '  <main class="page-shell narrow-shell">',
                    '    <p class="eyebrow">Canonical Pages Projection</p>',
                    "    <h1>Canonical project version</h1>",
                    "    <p>This historical link now resolves to the project's "
                    "explicit canonical version.</p>",
                    f'    <p><a href="{escaped_target}">Open canonical version</a></p>',
                    f'    <p><a class="back-link" href="{home}">'
                    "Back to ReasBook</a></p>",
                    "  </main>",
                    "</body>",
                    "</html>",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _validate_required_content(
        spec: ReleaseSpec,
        site: Path,
        routes: dict[str, tuple[Path | None, Path | None]],
    ) -> None:
        required = [site / "index.html", site / "release-spec.json"]
        for project in spec.canonical_projects():
            required.append(site / "sites" / project.slug / "index.html")
            pages, docs = routes[project.key]
            if pages is not None:
                required.append(site / pages / "index.html")
            if "docs" in project.outputs:
                if docs is None:
                    raise DeployExecutionError(
                        f"Pages projection has no canonical API entry: {project.key}"
                    )
                required.append(site / docs)
            if "theorem_graph" in project.outputs:
                required.append(
                    site / "theorem-maps" / project.kind / project.slug / "index.html"
                )
        missing = [
            str(path.relative_to(site)) for path in required if not path.is_file()
        ]
        if missing:
            raise DeployExecutionError(
                "Pages projection is missing canonical content: " + ", ".join(missing)
            )

    @staticmethod
    def _validate_site(root: Path) -> None:
        if not root.is_dir() or root.is_symlink():
            raise DeployExecutionError(f"site tree is not a directory: {root}")
        for path in root.rglob("*"):
            if path.is_symlink():
                raise DeployExecutionError(f"site tree contains a symlink: {path}")
            if not path.is_file() and not path.is_dir():
                raise DeployExecutionError(f"site tree contains a special file: {path}")

    @staticmethod
    def _publish(staged: Path, target: Path, backup: Path) -> None:
        had_target = target.exists() or target.is_symlink()
        if had_target:
            os.replace(target, backup)
        try:
            os.replace(staged, target)
        except OSError:
            if had_target and not (target.exists() or target.is_symlink()):
                os.replace(backup, target)
            raise
        if had_target:
            if backup.is_dir() and not backup.is_symlink():
                shutil.rmtree(backup)
            else:
                backup.unlink(missing_ok=True)


def create_release_set(
    layout: ReleaseLayout,
    store: ReleaseStore,
    spec: ReleaseSpec,
    policies: tuple[ReleaseArtifactPolicy, ...],
    bundles: tuple[BundleInfo, ...],
) -> tuple[ReleaseSetManifest, tuple[BundleInfo, ...]]:
    """Persist a portable manifest that binds both target artifacts."""

    records: list[ReleaseArtifactRecord] = []
    for bundle in sorted(bundles, key=lambda item: item.artifact):
        value = json.loads(Path(bundle.manifest).read_text(encoding="utf-8"))
        manifest = ReleaseManifest.from_dict(value)
        if (
            bundle.release_id != spec.release_id
            or manifest.release_id != spec.release_id
            or manifest.spec_digest != spec.spec_digest
            or manifest.artifact != bundle.artifact
        ):
            raise DeployExecutionError("artifact manifest does not match its bundle")
        records.append(
            ReleaseArtifactRecord(
                name=bundle.artifact,
                bundle=Path(bundle.bundle).name,
                bundle_sha256=bundle.bundle_sha256,
                site_tree_sha256=manifest.site_tree_sha256,
                file_count=manifest.file_count,
                total_bytes=manifest.total_bytes,
            )
        )
    release_set = ReleaseSetManifest(
        release_id=spec.release_id,
        spec_digest=spec.spec_digest,
        generated_at=spec.resolved_at,
        artifact_policy_sha256=artifact_policy_digest(policies),
        artifacts=tuple(records),
    )
    store.write_release_set(release_set)
    updated = tuple(
        replace(bundle, release_set=str(layout.release_set)) for bundle in bundles
    )
    for bundle in updated:
        if bundle.artifact == "pages":
            store.write_pages_bundle_info(bundle)
        elif bundle.artifact == "full":
            store.write_bundle_info(bundle)
    return release_set, updated


__all__ = [
    "PagesSiteProjector",
    "artifact_policy_digest",
    "create_release_set",
]
