"""Local acceptance gate for immutable static release artifacts.

The gate deliberately composes the existing bundle verifier, preview server,
and self-hosted installer.  It does not build source or implement a second
hosting stack.
"""

from __future__ import annotations

import ast
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import importlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Iterator
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urljoin, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener, urlopen
import uuid

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployConfigError, DeployExecutionError
from .artifacts import README_URL, artifact_policy_digest
from .bundle import BundleVerifier, normalize_sha256
from .models import (
    ProjectSpec,
    ReleaseArtifactPolicy,
    ReleaseSpec,
    default_artifact_policies,
)
from .results import (
    BundleInfo,
    ReleaseManifest,
    ReleasePackageResult,
    ReleaseSetManifest,
)
from .self_hosted import SelfHostedInstaller
from .store import ReleaseLayout, ReleaseStore
from .tooling import (
    tooling_digest_from_revision,
    tooling_snapshot_digest,
    tooling_source_digest,
)


_BROWSER_MODES = {"auto", "required", "skip"}
_PRODUCTION_ROUTING_MODE = "strict"
_README_REDIRECT_KINDS = {"root", "versions", "version-branch", "docs-index", "project"}
_VERSO_EMPTY_MARKERS = (
    "no separate reading sections are published for this version.",
    "directory: no section modules discovered yet.",
    "todo: no chapter/section modules discovered yet",
    "todo: no section modules discovered yet",
)
_VERSO_EMPTY_ATTRIBUTE_RE = re.compile(
    r"""\bdata-reasbook-verso-empty\s*=\s*(?:
        "\s*true\s*"
        |'\s*true\s*'
        |true(?=[\s/>])
    )""",
    flags=re.IGNORECASE | re.VERBOSE,
)
_VERSO_DIRECTORY_LABELS = {
    "chapter index",
    "directory",
    "section index",
}
_VERSO_MAX_LINK_DEPTH = 12
_VERSO_VISITING = 1
_VERSO_VALIDATED = 2
_META_REFRESH_RE = re.compile(
    r"^\s*(?P<delay>\d+(?:\.\d+)?)\s*;\s*url\s*=\s*(?P<target>.*?)\s*$",
    flags=re.IGNORECASE,
)


class _VersoReadableContent(Exception):
    """Internal parser short-circuit after proving a non-root content leaf."""


class _VersoContentProbe(HTMLParser):
    """Collect standalone reading prose from the rendered Verso article."""

    _READABLE_TAGS = {"blockquote", "figure", "p", "pre", "table"}
    _HIDDEN_TAGS = {"nav", "script", "style", "template"}
    _VOID_TAGS = {
        "area",
        "base",
        "br",
        "col",
        "embed",
        "hr",
        "img",
        "input",
        "link",
        "meta",
        "param",
        "source",
        "track",
        "wbr",
    }
    _HIDDEN_STYLE_RE = re.compile(
        r"(?:^|;)\s*(?:display\s*:\s*none|visibility\s*:\s*hidden)"
        r"\s*(?:!important\s*)?(?:;|$)",
        flags=re.IGNORECASE,
    )

    def __init__(self, *, stop_after_readable: bool = False) -> None:
        super().__init__(convert_charrefs=True)
        # Verso's generated wrapper changed across supported Lean branches.
        # Newer output uses ``article``; older output uses a ``div`` carrying
        # ``role="main"``.  The element stack keeps both the content-root
        # lifetime and inherited hidden state correct across nested elements,
        # including nested elements with the same tag name.
        self._content_root_tag: str | None = None
        self._element_stack: list[tuple[str, bool]] = []
        self._hidden_depth = 0
        self._list_depth = 0
        self._readable_depth = 0
        self._current: list[str] = []
        self.paragraphs: list[str] = []
        self.links: list[str] = []
        self.anchors: list[str] = []
        self.refresh_meta_count = 0
        self.refreshes: list[tuple[float, str]] = []
        self.explicitly_empty = False
        self.standalone = False
        self._stop_after_readable = stop_after_readable

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        tag = tag.lower()
        normalized_attrs = {
            name.casefold(): (value or "").strip().casefold() for name, value in attrs
        }
        exact_attrs = {name.casefold(): value or "" for name, value in attrs}
        self.explicitly_empty |= (
            normalized_attrs.get("data-reasbook-verso-empty") == "true"
        )
        self.standalone |= (
            normalized_attrs.get("data-reasbook-verso-standalone") == "true"
        )
        if tag == "meta" and normalized_attrs.get("http-equiv") == "refresh":
            self.refresh_meta_count += 1
            match = _META_REFRESH_RE.fullmatch(exact_attrs.get("content", ""))
            if match and match.group("target"):
                target = match.group("target").strip("\"'")
                if target:
                    self.refreshes.append((float(match.group("delay")), target))
        if tag == "a" and exact_attrs.get("href"):
            self.anchors.append(exact_attrs["href"])
        starts_hidden_scope = (
            tag in self._HIDDEN_TAGS
            or "hidden" in normalized_attrs
            or normalized_attrs.get("aria-hidden") == "true"
            or self._HIDDEN_STYLE_RE.search(exact_attrs.get("style", "")) is not None
        )
        if self._content_root_tag is None:
            if tag in {"article", "main"} or normalized_attrs.get("role") == "main":
                self._content_root_tag = tag
                self._push_element(tag, starts_hidden_scope)
            return
        self._push_element(tag, starts_hidden_scope)
        if self._hidden_depth:
            return
        if tag == "a":
            href = exact_attrs.get("href")
            if href:
                self.links.append(href)
        if tag in {"ol", "ul"}:
            self._list_depth += 1
        if tag in self._READABLE_TAGS and not self._list_depth:
            if not self._readable_depth:
                self._current = []
            self._readable_depth += 1

    def handle_endtag(self, tag: str) -> None:
        tag = tag.lower()
        if self._content_root_tag is None:
            return
        if tag in self._VOID_TAGS:
            return
        was_hidden = bool(self._hidden_depth)
        try:
            if not was_hidden:
                if tag in self._READABLE_TAGS and self._readable_depth:
                    self._readable_depth -= 1
                    if not self._readable_depth:
                        text = " ".join(" ".join(self._current).split())
                        if text:
                            self.paragraphs.append(text)
                            normalized = text.casefold().strip(" .:-")
                            if (
                                self._stop_after_readable
                                and normalized
                                and normalized not in _VERSO_DIRECTORY_LABELS
                            ):
                                raise _VersoReadableContent
                        self._current = []
                if tag in {"ol", "ul"}:
                    self._list_depth = max(0, self._list_depth - 1)
        finally:
            self._pop_element(tag)

    def _push_element(self, tag: str, starts_hidden_scope: bool) -> None:
        """Record one non-void element and its contribution to hidden state."""

        if tag in self._VOID_TAGS:
            return
        self._element_stack.append((tag, starts_hidden_scope))
        if starts_hidden_scope:
            self._hidden_depth += 1

    def _pop_element(self, tag: str) -> None:
        """Close the innermost matching element without losing hidden ancestry."""

        match = next(
            (
                index
                for index in range(len(self._element_stack) - 1, -1, -1)
                if self._element_stack[index][0] == tag
            ),
            None,
        )
        if match is None:
            return
        removed = self._element_stack[match:]
        del self._element_stack[match:]
        self._hidden_depth = max(
            0,
            self._hidden_depth - sum(1 for _removed_tag, hidden in removed if hidden),
        )
        if not self._element_stack:
            self._content_root_tag = None

    def handle_data(self, data: str) -> None:
        if (
            self._content_root_tag is not None
            and not self._hidden_depth
            and self._readable_depth
            and not self._list_depth
        ):
            self._current.append(data)


@dataclass(frozen=True)
class _Route:
    kind: str
    path: str


class _NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class ReleaseAcceptanceRunner:
    """Verify and exercise both artifacts without Docker or a source build."""

    def __init__(
        self,
        repo_root: Path,
        layout: ReleaseLayout,
        spec: ReleaseSpec,
        *,
        expected_artifact_policy_sha256: str,
        artifact_policies: tuple[ReleaseArtifactPolicy, ...] | None = None,
    ) -> None:
        self.repo_root = Path(repo_root).expanduser().resolve()
        self.layout = layout
        self.spec = spec
        expected = normalize_sha256(expected_artifact_policy_sha256)
        assert expected is not None
        self.expected_policy = expected
        policies = artifact_policies or default_artifact_policies()
        if normalize_sha256(artifact_policy_digest(policies)) != expected:
            raise DeployConfigError(
                "acceptance artifact policies do not match the expected digest"
            )
        by_name = {policy.name: policy for policy in policies}
        if set(by_name) != {"full", "pages"} or len(by_name) != len(policies):
            raise DeployConfigError(
                "acceptance requires exactly the full and pages artifact policies"
            )
        self.verifiers = {
            name: BundleVerifier.for_policy(policy) for name, policy in by_name.items()
        }
        self.preview_script = self.repo_root / "scripts" / "preview" / "serve.py"
        if not self.preview_script.is_file():
            raise DeployConfigError(
                f"release preview adapter does not exist: {self.preview_script}"
            )
        self.verso_exemptions = self._load_bound_verso_exemptions()

    def run(
        self,
        *,
        browser_mode: str = "auto",
        keep_workdir: bool = False,
    ) -> dict[str, Any]:
        """Run the complete local gate and return machine-readable evidence.

        Successful runs retain their small logs, screenshots, and result JSON,
        while extracted trees are removed unless ``keep_workdir`` is true.  A
        failed run keeps its scratch tree so the exact served artifacts remain
        available for diagnosis.
        """

        if browser_mode not in _BROWSER_MODES:
            raise DeployConfigError(
                "browser mode must be one of auto, required, or skip"
            )
        if not isinstance(keep_workdir, bool):
            raise DeployConfigError("keep_workdir must be boolean")

        run_root = self._new_run_root()
        scratch = run_root / "scratch"
        logs = run_root / "logs"
        screenshots = run_root / "screenshots"
        scratch.mkdir()
        logs.mkdir()
        screenshots.mkdir()

        try:
            package, release_set = self._load_package()
            pages_site = scratch / "pages"
            pages_manifest = self.verifiers["pages"].verify(
                Path(package.pages.bundle),
                expected_sha256=package.pages.bundle_sha256,
                extract_to=pages_site,
            )
            full_manifest = self.verifiers["full"].inspect(
                Path(package.full.bundle),
                expected_sha256=package.full.bundle_sha256,
            )
            manifests = {
                "pages": pages_manifest,
                "full": full_manifest,
            }
            self._validate_binding(
                release_set,
                package.pages,
                pages_manifest,
            )
            self._validate_binding(
                release_set,
                package.full,
                full_manifest,
            )

            deployment = SelfHostedInstaller(
                scratch / "self-hosted",
                verifier=self.verifiers["full"],
            ).install(
                Path(package.full.bundle),
                release_set=self.layout.release_set,
                expected_sha256=package.full.bundle_sha256,
                expected_artifact_policy_sha256=self.expected_policy,
                filesystem_health_only=True,
            )
            full_site = Path(deployment.active_site)

            artifacts: dict[str, Any] = {}
            for name, site, manifest in (
                ("pages", pages_site, pages_manifest),
                ("full", full_site, full_manifest),
            ):
                routes = self._routes(site, artifact=name)
                with self._preview_server(
                    site,
                    logs / f"{name}-preview.log",
                ) as origin:
                    http = self._http_smoke(origin, routes, manifest)
                    browser = self._browser_smoke(
                        origin,
                        routes,
                        name=name,
                        mode=browser_mode,
                        screenshots=screenshots,
                    )
                artifacts[name] = {
                    "bundle": str(
                        package.pages.bundle if name == "pages" else package.full.bundle
                    ),
                    "bundle_sha256": (
                        package.pages.bundle_sha256
                        if name == "pages"
                        else package.full.bundle_sha256
                    ),
                    "site_tree_sha256": manifest.site_tree_sha256,
                    "file_count": manifest.file_count,
                    "total_bytes": manifest.total_bytes,
                    "http": http,
                    "browser": browser,
                    "routing_mode": _PRODUCTION_ROUTING_MODE,
                }

            metadata = self._metadata_evidence(
                package,
                release_set,
                manifests,
            )
            if not keep_workdir:
                self._remove_scratch(run_root, scratch)
            result = {
                "status": "success",
                "release_id": self.spec.release_id,
                "spec_digest": self.spec.spec_digest,
                "artifact_policy_sha256": release_set.artifact_policy_sha256,
                "diagnostics_root": str(run_root),
                "scratch_retained": keep_workdir,
                "artifacts": artifacts,
                "metadata": metadata,
                "self_hosted": {
                    "status": "success",
                    "release_id": deployment.release_id,
                    "filesystem_health": "passed",
                },
            }
            self._write_result(run_root, result)
            return result
        except Exception as exc:
            failure = {
                "status": "failed",
                "release_id": self.spec.release_id,
                "spec_digest": self.spec.spec_digest,
                "diagnostics_root": str(run_root),
                "scratch_retained": True,
                "error": str(exc),
            }
            self._write_result(run_root, failure)
            raise DeployExecutionError(
                "release acceptance failed; diagnostics retained at "
                f"{run_root}: {exc}"
            ) from exc

    def _load_package(
        self,
    ) -> tuple[ReleasePackageResult, ReleaseSetManifest]:
        store = ReleaseStore(self.layout)
        release_set = store.load_release_set()
        actual_policy = normalize_sha256(release_set.artifact_policy_sha256)
        if actual_policy != self.expected_policy:
            raise DeployExecutionError(
                "ReleaseSet artifact policy differs from the trusted profile"
            )
        package = ReleasePackageResult(
            store.load_bundle_info(),
            store.load_pages_bundle_info(),
            release_set,
        )
        return package, release_set

    def _metadata_evidence(
        self,
        package: ReleasePackageResult,
        release_set: ReleaseSetManifest,
        manifests: dict[str, ReleaseManifest],
    ) -> dict[str, Any]:
        """Bind every portable metadata file to the bytes acceptance checked."""

        release_set_path = self.layout.release_set.resolve(strict=False)
        if (
            self.layout.release_set.is_symlink()
            or not self.layout.release_set.is_file()
        ):
            raise DeployExecutionError("ReleaseSet is not a regular file")
        try:
            release_set_bytes = release_set_path.read_bytes()
            release_set_value = json.loads(release_set_bytes)
            if not isinstance(release_set_value, dict):
                raise DeployConfigError("ReleaseSet must be an object")
            current_release_set = ReleaseSetManifest.from_dict(release_set_value)
        except (OSError, UnicodeError, json.JSONDecodeError, DeployConfigError) as exc:
            raise DeployExecutionError("ReleaseSet changed during acceptance") from exc
        if current_release_set != release_set:
            raise DeployExecutionError("ReleaseSet changed during acceptance")

        artifacts: dict[str, Any] = {}
        for name, bundle in (("full", package.full), ("pages", package.pages)):
            manifest_path = Path(bundle.manifest).expanduser().resolve(strict=False)
            checksums_path = Path(bundle.checksums).expanduser().resolve(strict=False)
            bundle_path = Path(bundle.bundle).expanduser().resolve(strict=False)
            for label, path in (
                ("manifest", manifest_path),
                ("checksums", checksums_path),
            ):
                if path.is_symlink() or not path.is_file():
                    raise DeployExecutionError(f"{name} {label} is not a regular file")

            external_manifest = manifest_path.read_bytes()
            embedded_manifest = self.verifiers[name].release_manifest_bytes(
                bundle_path,
                expected_sha256=bundle.bundle_sha256,
            )
            try:
                external_value = json.loads(external_manifest)
                if not isinstance(external_value, dict):
                    raise DeployConfigError("release manifest must be an object")
                parsed_manifest = ReleaseManifest.from_dict(external_value)
            except (UnicodeError, json.JSONDecodeError, DeployConfigError) as exc:
                raise DeployExecutionError(
                    f"{name} external release manifest is invalid"
                ) from exc
            if (
                external_manifest != embedded_manifest
                or parsed_manifest != manifests[name]
            ):
                raise DeployExecutionError(
                    f"{name} external release manifest differs from its bundle"
                )

            expected_digest = normalize_sha256(bundle.bundle_sha256)
            assert expected_digest is not None
            expected_checksums = f"{expected_digest}  {bundle_path.name}\n".encode(
                "utf-8"
            )
            checksums = checksums_path.read_bytes()
            if checksums != expected_checksums:
                raise DeployExecutionError(
                    f"{name} checksum metadata differs from its bundle"
                )
            artifacts[name] = {
                "manifest": str(manifest_path),
                "manifest_sha256": (
                    "sha256:" + hashlib.sha256(external_manifest).hexdigest()
                ),
                "checksums": str(checksums_path),
                "checksums_sha256": ("sha256:" + hashlib.sha256(checksums).hexdigest()),
            }

        return {
            "release_set": str(release_set_path),
            "release_set_sha256": (
                "sha256:" + hashlib.sha256(release_set_bytes).hexdigest()
            ),
            "artifacts": artifacts,
        }

    def _validate_binding(
        self,
        release_set: ReleaseSetManifest,
        bundle: BundleInfo,
        manifest: ReleaseManifest,
    ) -> None:
        record = release_set.artifact(bundle.artifact)
        if (
            manifest.artifact != bundle.artifact
            or manifest.release_id != self.spec.release_id
            or manifest.spec_digest != self.spec.spec_digest
            or manifest.base_path != self.spec.base_path
            or record.bundle != Path(bundle.bundle).name
            or record.bundle_sha256 != bundle.bundle_sha256
            or record.site_tree_sha256 != manifest.site_tree_sha256
            or record.file_count != manifest.file_count
            or record.total_bytes != manifest.total_bytes
        ):
            raise DeployExecutionError(
                f"ReleaseSet does not bind the {bundle.artifact} artifact"
            )

    def _routes(self, site: Path, *, artifact: str) -> tuple[_Route, ...]:
        if artifact not in {"full", "pages"}:
            raise DeployConfigError(f"unsupported acceptance artifact: {artifact}")
        site = site.resolve()
        routes = [_Route("root", self.spec.base_path)]

        def add_required_directory(kind: str, relative: Path) -> None:
            index = site / relative / "index.html"
            if not index.is_file() or index.is_symlink():
                raise DeployExecutionError(
                    f"{kind} route has no regular index: {relative.as_posix()}/"
                )
            route = self.spec.base_path + relative.as_posix().strip("/") + "/"
            routes.append(_Route(kind, route))

        def add_required_file(kind: str, relative: Path) -> None:
            target = site / relative
            if not target.is_file() or target.is_symlink():
                raise DeployExecutionError(
                    f"{kind} route has no regular file: {relative.as_posix()}"
                )
            route = self.spec.base_path + relative.as_posix().lstrip("/")
            routes.append(_Route(kind, route))

        def add_first_directory(kind: str, candidates: tuple[Path, ...]) -> Path:
            for relative in candidates:
                index = site / relative / "index.html"
                if index.is_file() and not index.is_symlink():
                    add_required_directory(kind, relative)
                    return relative
            rendered = ", ".join(f"{relative.as_posix()}/" for relative in candidates)
            raise DeployExecutionError(
                f"{kind} route has no regular index in: {rendered}"
            )

        def add_first_file(kind: str, candidates: tuple[Path, ...]) -> None:
            for relative in candidates:
                target = site / relative
                if target.is_file() and not target.is_symlink():
                    add_required_file(kind, relative)
                    return
            rendered = ", ".join(relative.as_posix() for relative in candidates)
            raise DeployExecutionError(
                f"{kind} route has no regular file in: {rendered}"
            )

        static = site / "static" / "catalog.css"
        if not static.is_file() or static.is_symlink():
            raise DeployExecutionError("release site has no catalog stylesheet")
        routes.append(_Route("asset", self.spec.base_path + "static/catalog.css"))

        if self.spec.include_historical_versions:
            add_required_directory("versions", Path("versions"))
            for branch in self.spec.branches:
                add_required_directory(
                    "version-branch",
                    Path("versions") / branch.name,
                )
        if self.spec.policy.require_docs:
            add_required_directory("docs-index", Path("docs"))

        for project in self.spec.canonical_projects():
            project_root = Path("sites") / project.slug
            add_required_directory("project", project_root)
            if "docs" in project.outputs:
                add_required_directory("docs", project_root / "docs")
            verso = site / project_root / "pages" / "index.html"
            if self._requires_verso(project):
                add_required_directory("verso", project_root / "pages")
                if artifact == "pages":
                    direct_verso = add_first_directory(
                        "canonical-verso-target",
                        self._direct_verso_roots(project),
                    )
                    self._validate_verso_adapter(
                        site,
                        project_root / "pages",
                        direct_verso,
                        project,
                    )
                    self._validate_verso_content(site, direct_verso, project)
                elif not self.spec.include_historical_versions:
                    direct_verso = add_first_directory(
                        "canonical-verso-target",
                        self._direct_verso_roots(project),
                    )
                    self._validate_verso_content(site, direct_verso, project)
            elif verso.is_file() and not verso.is_symlink():
                # Exercise an optional page when a formerly exempt project
                # starts publishing one, without treating it as required yet.
                add_required_directory("verso", project_root / "pages")
            if "theorem_graph" in project.outputs:
                add_required_directory(
                    "theorem-map",
                    Path("theorem-maps") / project.kind / project.slug,
                )

        if self.spec.include_historical_versions:
            projects = (
                self.spec.projects
                if artifact == "full"
                else self.spec.canonical_projects()
            )
            for project in projects:
                version_root = Path("versions") / project.branch
                if self._requires_verso(project) and artifact == "full":
                    direct_verso = add_first_directory(
                        "version-verso",
                        (
                            version_root / project.kind / project.slug,
                            version_root / project.slug,
                        ),
                    )
                    self._validate_verso_content(site, direct_verso, project)
                if "docs" in project.outputs:
                    kind_title = "Books" if project.kind == "books" else "Papers"
                    leaf = "Book.html" if project.kind == "books" else "Paper.html"
                    add_first_file(
                        "version-docs",
                        (
                            version_root
                            / "docs"
                            / "ReasBook"
                            / kind_title
                            / project.project_id
                            / leaf,
                            version_root
                            / "docs"
                            / "ReasBook"
                            / project.project_id
                            / leaf,
                            version_root
                            / "docs"
                            / kind_title
                            / project.project_id
                            / leaf,
                            version_root / "docs" / project.project_id / leaf,
                            version_root
                            / "docs"
                            / "ReasBook"
                            / f"{project.project_id}.html",
                            version_root / "docs" / f"{project.project_id}.html",
                        ),
                    )
                if "theorem_graph" in project.outputs:
                    add_required_directory(
                        "version-theorem-map",
                        version_root / "theorem-maps" / project.kind / project.slug,
                    )
        return tuple(routes)

    def _requires_verso(self, project: ProjectSpec) -> bool:
        return (
            "verso" in project.outputs
            and (project.key, project.branch) not in self.verso_exemptions
        )

    def _direct_verso_roots(self, project: ProjectSpec) -> tuple[Path, ...]:
        prefix = (
            Path("versions") / project.branch
            if self.spec.include_historical_versions
            else Path()
        )
        return (
            prefix / project.kind / project.slug,
            prefix / project.slug,
        )

    def _validate_verso_adapter(
        self,
        site: Path,
        adapter: Path,
        direct: Path,
        project: ProjectSpec,
    ) -> None:
        """Bind the canonical Pages adapter to its immutable direct route."""

        page = adapter / "index.html"
        _, probe = self._read_verso_page(site / page, project)
        expected = direct / "index.html"
        if (
            probe.refresh_meta_count != 1
            or len(probe.refreshes) != 1
            or probe.refreshes[0][0] != 0
        ):
            raise DeployExecutionError(
                "canonical Verso adapter must contain exactly one valid "
                f"zero-second meta refresh for {project.key}@{project.branch}"
            )
        refresh = self._local_html_target(site, page, probe.refreshes[0][1])
        if refresh != expected:
            raise DeployExecutionError(
                "canonical Verso adapter refresh does not target "
                f"{direct.as_posix()}/ for {project.key}@{project.branch}"
            )
        if not any(
            self._local_html_target(site, page, href) == expected
            for href in probe.anchors
        ):
            raise DeployExecutionError(
                "canonical Verso adapter has no anchor targeting "
                f"{direct.as_posix()}/ for {project.key}@{project.branch}"
            )
        if expected.is_absolute() or (site / expected).is_symlink():
            raise DeployExecutionError(
                f"canonical Verso adapter target is unsafe: {expected}"
            )
        if not (site / expected).is_file():
            raise DeployExecutionError(
                f"canonical Verso adapter target does not exist: {expected}"
            )

    def _validate_verso_content(
        self,
        site: Path,
        relative: Path,
        project: ProjectSpec,
    ) -> None:
        """Reject a generated Verso shell that has no readable project content.

        ``sites/<slug>/pages`` is a canonical redirect adapter, so the content
        contract is intentionally enforced on the direct route selected by
        ``_routes``.  A normal book or paper has at least one chapter/section
        route.  A deliberately single-page work must instead carry an explicit
        standalone marker and prose inside ``article``, ``main``, or
        ``role=main``.
        """

        self._validate_verso_page(
            site,
            relative / "index.html",
            project,
            states={},
            depth=0,
            is_root=True,
        )

    def _validate_verso_page(
        self,
        site: Path,
        page: Path,
        project: ProjectSpec,
        *,
        states: dict[Path, int],
        depth: int,
        is_root: bool,
    ) -> None:
        if depth > _VERSO_MAX_LINK_DEPTH:
            raise DeployExecutionError(
                "Verso content directory exceeds the maximum link depth for "
                f"{project.key}@{project.branch}: {page.as_posix()}"
            )
        state = states.get(page)
        if state == _VERSO_VALIDATED:
            return
        if state == _VERSO_VISITING:
            raise DeployExecutionError(
                "Verso content directory contains a redirect cycle for "
                f"{project.key}@{project.branch}: {page.as_posix()}"
            )
        states[page] = _VERSO_VISITING

        payload, probe = self._read_verso_page(
            site / page,
            project,
            stop_after_readable=not is_root,
        )
        folded_payload = payload.casefold()
        marker = (
            "data-reasbook-verso-empty=true"
            if _VERSO_EMPTY_ATTRIBUTE_RE.search(payload)
            else next(
                (item for item in _VERSO_EMPTY_MARKERS if item in folded_payload),
                None,
            )
        )
        if marker is not None or probe.explicitly_empty:
            raise DeployExecutionError(
                "version-verso is an explicit empty shell for "
                f"{project.key}@{project.branch}: "
                f"{marker or 'data-reasbook-verso-empty'}"
            )

        readable = any(
            (normalized := paragraph.casefold().strip(" .:-"))
            and normalized not in _VERSO_DIRECTORY_LABELS
            for paragraph in probe.paragraphs
        )
        if probe.refresh_meta_count:
            if (
                probe.refresh_meta_count != 1
                or len(probe.refreshes) != 1
                or probe.refreshes[0][0] != 0
            ):
                raise DeployExecutionError(
                    "Verso content redirect is not a single zero-second "
                    f"refresh: {page.as_posix()}"
                )
            target = self._project_verso_target(
                site,
                page,
                project,
                probe.refreshes[0][1],
            )
            if target is None or not any(
                self._project_verso_target(site, page, project, href) == target
                for href in probe.anchors
            ):
                raise DeployExecutionError(
                    "Verso content redirect has no matching project anchor: "
                    f"{page.as_posix()}"
                )
            self._validate_verso_page(
                site,
                target,
                project,
                states=states,
                depth=depth + 1,
                is_root=is_root,
            )
            states[page] = _VERSO_VALIDATED
            return

        # Rendered theorem/definition pages contain many cross-links into the
        # same project.  Once a non-root page has real prose it is a content
        # leaf for this gate; walking those ordinary links turns a shared DAG
        # into exponential repeated work and adds no stronger evidence.
        if readable and not is_root:
            states[page] = _VERSO_VALIDATED
            return
        if readable and probe.standalone:
            states[page] = _VERSO_VALIDATED
            return

        children = {
            target
            for href in probe.links
            if (
                target := self._project_verso_target(
                    site,
                    page,
                    project,
                    href,
                )
            )
            is not None
            and target != page
            # Ordinary content links commonly include a Book home backlink.
            # They are not redirect edges, so ignore a grey ancestor rather
            # than reporting a cycle.  With no remaining forward child the
            # directory still falls through to the empty-leaf failure below.
            and states.get(target) != _VERSO_VISITING
        }
        if children:
            for child in sorted(children, key=lambda item: item.as_posix()):
                self._validate_verso_page(
                    site,
                    child,
                    project,
                    states=states,
                    depth=depth + 1,
                    is_root=False,
                )
            states[page] = _VERSO_VALIDATED
            return

        detail = "explicit standalone marker and readable prose" if is_root else "prose"
        raise DeployExecutionError(
            "version-verso has no readable chapter, section, or standalone "
            f"content for {project.key}@{project.branch}: {page.as_posix()} "
            f"(leaf requires {detail})"
        )

    def _read_verso_page(
        self,
        page: Path,
        project: ProjectSpec,
        *,
        stop_after_readable: bool = False,
    ) -> tuple[str, _VersoContentProbe]:
        if page.is_symlink() or not page.is_file():
            raise DeployExecutionError(
                "Verso content page is not a regular file for "
                f"{project.key}@{project.branch}: {page}"
            )
        try:
            payload = page.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            raise DeployExecutionError(
                "Verso content page cannot be read for "
                f"{project.key}@{project.branch}: {page}"
            ) from exc
        if "<html" not in payload.casefold():
            raise DeployExecutionError(
                "Verso content page is not HTML for "
                f"{project.key}@{project.branch}: {page}"
            )
        # A redirect must be parsed in full.  Ordinary content pages can stop
        # at their first real prose block; the raw empty markers were already
        # retained in ``payload`` for the caller's fail-closed check.
        can_short_circuit = (
            stop_after_readable and "http-equiv" not in payload.casefold()
        )
        probe = _VersoContentProbe(stop_after_readable=can_short_circuit)
        try:
            probe.feed(payload)
            probe.close()
        except _VersoReadableContent:
            pass
        except (UnicodeError, ValueError) as exc:
            raise DeployExecutionError(
                "Verso content page is invalid HTML for "
                f"{project.key}@{project.branch}: {page}"
            ) from exc
        return payload, probe

    def _project_verso_target(
        self,
        site: Path,
        page: Path,
        project: ProjectSpec,
        href: str,
    ) -> Path | None:
        target = self._local_html_target(site, page, href)
        if target is None:
            return None
        for scope in self._direct_verso_roots(project):
            try:
                target.relative_to(scope)
            except ValueError:
                continue
            return target
        return None

    def _local_html_target(
        self,
        site: Path,
        page: Path,
        href: str,
    ) -> Path | None:
        route = self.spec.base_path + page.as_posix().lstrip("/")
        try:
            parsed = urlsplit(urljoin(route, href))
        except ValueError:
            return None
        if (
            parsed.scheme
            or parsed.netloc
            or not parsed.path.startswith(self.spec.base_path)
        ):
            return None
        candidate = Path(unquote(parsed.path[len(self.spec.base_path) :]).lstrip("/"))
        if candidate.is_absolute() or ".." in candidate.parts:
            return None
        if parsed.path.endswith("/") or not candidate.suffix:
            candidate /= "index.html"
        elif candidate.suffix.casefold() not in {".htm", ".html"}:
            return None
        # ``site`` is intentionally part of the signature: callers resolve
        # only against the extracted artifact, never the checkout filesystem.
        if (site / candidate).is_symlink():
            return None
        return candidate

    def _load_bound_verso_exemptions(self) -> frozenset[tuple[str, str]]:
        """Read capabilities only from tooling bound to this ReleaseSpec.

        ReleaseSpec v1 applies the global Verso policy to every project, so it
        cannot yet represent the one intentional per-project exception.  The
        exception therefore comes from the immutable tooling snapshot used by
        the build.  A matching current checkout is an allowed fallback for
        local canaries that did not materialize a snapshot.
        """

        expected_digest = tooling_digest_from_revision(self.spec.tooling_revision)
        snapshot = self.layout.root / "tooling-snapshots" / expected_digest
        if snapshot.exists() or snapshot.is_symlink():
            actual_digest = tooling_snapshot_digest(snapshot)
            if actual_digest != expected_digest:
                raise DeployConfigError(
                    "release tooling snapshot differs from ReleaseSpec"
                )
            tooling_root = snapshot
        else:
            actual_digest = tooling_source_digest(self.repo_root)
            if actual_digest != expected_digest:
                raise DeployConfigError(
                    "current tooling differs from ReleaseSpec and no matching "
                    "release snapshot is available"
                )
            tooling_root = self.repo_root

        path = tooling_root / "scripts" / "pages" / "project_catalog.py"
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, SyntaxError, UnicodeError) as exc:
            raise DeployConfigError(
                f"cannot load project capability registry: {path}"
            ) from exc
        value: object = None
        for node in tree.body:
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if any(
                isinstance(target, ast.Name) and target.id == "NO_VERSO_PROJECTS"
                for target in targets
            ):
                try:
                    value = ast.literal_eval(node.value)
                except (ValueError, TypeError) as exc:
                    raise DeployConfigError(
                        "project capability registry must define "
                        "NO_VERSO_PROJECTS as a literal set"
                    ) from exc
                break
        if not isinstance(value, set) or any(
            not isinstance(item, str) or not item for item in value
        ):
            raise DeployConfigError(
                f"project capability registry has invalid NO_VERSO_PROJECTS: {path}"
            )
        return frozenset(
            (project.key, project.branch)
            for project in self.spec.projects
            if project.project_id in value
        )

    def _http_smoke(
        self,
        origin: str,
        routes: tuple[_Route, ...],
        manifest: ReleaseManifest,
    ) -> dict[str, Any]:
        checked: list[str] = []
        for route in routes:
            request = Request(
                origin + route.path,
                headers={"User-Agent": "ReasBook-E2E/1"},
            )
            try:
                with urlopen(request, timeout=10.0) as response:
                    status = response.status
                    content_type = response.headers.get_content_type()
                    payload = response.read(1_048_576)
                    final_url = response.geturl()
            except (OSError, URLError, HTTPError) as exc:
                raise DeployExecutionError(
                    f"HTTP smoke failed for {route.path}: {exc}"
                ) from exc
            if status != 200 or not payload:
                raise DeployExecutionError(
                    f"HTTP smoke received an invalid response for {route.path}"
                )
            expected_url = origin + route.path
            if final_url != expected_url:
                raise DeployExecutionError(
                    f"HTTP smoke redirected {route.path} to {final_url!r}"
                )
            if route.kind == "asset":
                if content_type != "text/css":
                    raise DeployExecutionError(
                        f"HTTP smoke expected CSS at {route.path}, got {content_type}"
                    )
            elif content_type != "text/html" or b"<html" not in payload.lower():
                raise DeployExecutionError(
                    f"HTTP smoke expected HTML at {route.path}, got {content_type}"
                )
            checked.append(route.path)

        spec_path = self.spec.base_path + "release-spec.json"
        health = self._read_json(origin + spec_path)
        if (
            health.get("release_id") != manifest.release_id
            or health.get("spec_digest") != manifest.spec_digest
        ):
            raise DeployExecutionError("preview reports another ReleaseSpec")

        missing_path = self.spec.base_path + "__reasbook_e2e_missing__"
        try:
            urlopen(
                Request(
                    origin + missing_path,
                    headers={"User-Agent": "ReasBook-E2E/1"},
                ),
                timeout=10.0,
            ).close()
        except HTTPError as exc:
            if exc.code != 404:
                raise DeployExecutionError(
                    f"missing route returned HTTP {exc.code}, expected 404"
                ) from exc
        except (OSError, URLError) as exc:
            raise DeployExecutionError(f"missing-route smoke failed: {exc}") from exc
        else:
            raise DeployExecutionError("missing route did not return HTTP 404")

        opener = build_opener(_NoRedirect)
        try:
            response = opener.open(
                Request(origin + "/", headers={"User-Agent": "ReasBook-E2E/1"}),
                timeout=10.0,
            )
        except HTTPError as exc:
            if self.spec.base_path == "/":
                raise DeployExecutionError(
                    f"root-mounted preview returned HTTP {exc.code}"
                ) from exc
            if exc.code != 308:
                raise DeployExecutionError(
                    f"preview root returned HTTP {exc.code}, expected 308"
                ) from exc
            location = exc.headers.get("Location")
            if location != self.spec.base_path:
                raise DeployExecutionError(
                    f"preview root redirects to {location!r}, expected "
                    f"{self.spec.base_path!r}"
                )
        else:
            with response:
                if self.spec.base_path != "/":
                    raise DeployExecutionError(
                        "preview root did not redirect to the configured base path"
                    )
                if response.status != 200 or response.geturl() != origin + "/":
                    raise DeployExecutionError(
                        "root-mounted preview did not serve the site at /"
                    )
        base_path_redirect_status = None
        if self.spec.base_path != "/":
            path_without_slash = self.spec.base_path.rstrip("/")
            try:
                response = opener.open(
                    Request(
                        origin + path_without_slash,
                        headers={"User-Agent": "ReasBook-E2E/1"},
                    ),
                    timeout=10.0,
                )
            except HTTPError as exc:
                if exc.code != 308:
                    raise DeployExecutionError(
                        "preview base path without a trailing slash returned "
                        f"HTTP {exc.code}, expected 308"
                    ) from exc
                location = exc.headers.get("Location")
                if location != self.spec.base_path:
                    raise DeployExecutionError(
                        "preview base path without a trailing slash redirects "
                        f"to {location!r}, expected {self.spec.base_path!r}"
                    )
                base_path_redirect_status = exc.code
            else:
                response.close()
                raise DeployExecutionError(
                    "preview base path without a trailing slash did not redirect"
                )
        return {
            "status": "passed",
            "route_count": len(checked),
            "routes": checked,
            "release_spec": spec_path,
            "missing_route_status": 404,
            "base_path_redirect_status": base_path_redirect_status,
        }

    def _browser_smoke(
        self,
        origin: str,
        routes: tuple[_Route, ...],
        *,
        name: str,
        mode: str,
        screenshots: Path,
    ) -> dict[str, Any]:
        if mode == "skip":
            return {
                "status": "skipped",
                "reason": "disabled explicitly with --browser-mode skip",
            }
        try:
            playwright_api = importlib.import_module("playwright.sync_api")
        except ModuleNotFoundError as exc:
            if exc.name not in {"playwright", "playwright.sync_api"}:
                raise
            message = (
                "Playwright is not installed; install the deploy SDK e2e extra "
                "and Chromium"
            )
            if mode == "required":
                raise DeployExecutionError(message) from exc
            return {"status": "skipped", "reason": message}

        representative: list[_Route] = []
        represented_kinds: set[str] = set()
        for route in routes:
            if route.kind == "asset" or route.kind in represented_kinds:
                continue
            represented_kinds.add(route.kind)
            representative.append(route)

        console_errors: list[str] = []
        page_errors: list[str] = []
        failed_responses: list[str] = []
        failed_requests: list[str] = []
        checked_by_viewport: dict[str, list[str]] = {}
        screenshots.mkdir(parents=True, exist_ok=True)
        try:
            with playwright_api.sync_playwright() as playwright:
                browser_path = Path(playwright.chromium.executable_path)
                if not browser_path.is_file():
                    message = (
                        "Playwright Chromium is not installed; run "
                        "`./sdk/common/bin/python -m playwright install chromium`"
                    )
                    if mode == "required":
                        raise DeployExecutionError(message)
                    return {"status": "skipped", "reason": message}
                browser = playwright.chromium.launch(headless=True)
                try:
                    origin_parts = urlsplit(origin)

                    def is_same_origin(url: str) -> bool:
                        parts = urlsplit(url)
                        return (
                            parts.scheme == origin_parts.scheme
                            and parts.netloc == origin_parts.netloc
                        )

                    def record_response(response) -> None:
                        if is_same_origin(response.url) and response.status >= 400:
                            failed_responses.append(
                                f"HTTP {response.status} {response.url}"
                            )

                    def record_failed_request(request) -> None:
                        if is_same_origin(request.url):
                            detail = request.failure or "unknown network failure"
                            failed_requests.append(f"{detail}: {request.url}")

                    def attach_observers(page) -> None:
                        # Check the browser's actual redirect destination without
                        # depending on GitHub availability in local acceptance.
                        # Only this exact external target is intercepted; Docs
                        # and Verso are still required to stay inside the site.
                        page.route(
                            README_URL.split("#", 1)[0],
                            lambda request: request.fulfill(
                                status=200,
                                content_type="text/html",
                                body=(
                                    "<!doctype html><html><head>"
                                    "<title>ReasBook README redirect target</title>"
                                    "</head><body><p>ReasBook README</p></body></html>"
                                ),
                            ),
                        )
                        page.on(
                            "console",
                            lambda message: console_errors.append(message.text)
                            if message.type == "error"
                            else None,
                        )
                        page.on(
                            "pageerror",
                            lambda error: page_errors.append(str(error)),
                        )
                        page.on("response", record_response)
                        page.on("requestfailed", record_failed_request)

                    def exercise_viewport(
                        page,
                        *,
                        viewport_name: str,
                        screenshot_suffix: str,
                    ) -> None:
                        attach_observers(page)
                        checked: list[str] = []
                        for route in representative:
                            response = page.goto(
                                origin + route.path,
                                wait_until="networkidle",
                                timeout=30_000,
                            )
                            if response is None or response.status >= 400:
                                raise DeployExecutionError(
                                    f"browser navigation failed for {route.path}"
                                )
                            final_url = urlsplit(page.url)
                            expected_readme_redirect = (
                                route.kind in _README_REDIRECT_KINDS
                                and page.url == README_URL
                            )
                            if (
                                final_url.scheme != origin_parts.scheme
                                or final_url.netloc != origin_parts.netloc
                                or not final_url.path.startswith(self.spec.base_path)
                            ) and not expected_readme_redirect:
                                raise DeployExecutionError(
                                    "browser navigation escaped the site at "
                                    f"{route.path} ({viewport_name})"
                                )
                            dimensions = page.evaluate(
                                """() => ({
                                  scrollWidth: document.documentElement.scrollWidth,
                                  clientWidth: document.documentElement.clientWidth
                                })"""
                            )
                            if (
                                dimensions["scrollWidth"]
                                > dimensions["clientWidth"] + 2
                            ):
                                raise DeployExecutionError(
                                    "horizontal overflow at "
                                    f"{route.path} ({viewport_name}): "
                                    f"{dimensions['scrollWidth']} > "
                                    f"{dimensions['clientWidth']}"
                                )
                            if route.kind == "root":
                                if not page.title().strip():
                                    raise DeployExecutionError(
                                        "browser root page has an empty title"
                                    )
                                page.screenshot(
                                    path=str(
                                        screenshots / f"{name}-{screenshot_suffix}.png"
                                    ),
                                    full_page=True,
                                )
                            checked.append(route.path)
                        checked_by_viewport[viewport_name] = checked

                    page = browser.new_page(viewport={"width": 1440, "height": 1000})
                    exercise_viewport(
                        page,
                        viewport_name="1440x1000",
                        screenshot_suffix="desktop",
                    )
                    mobile = browser.new_page(
                        viewport={"width": 390, "height": 844},
                        device_scale_factor=1,
                    )
                    exercise_viewport(
                        mobile,
                        viewport_name="390x844",
                        screenshot_suffix="mobile",
                    )
                finally:
                    browser.close()
        except DeployExecutionError:
            raise
        except Exception as exc:
            raise DeployExecutionError(f"browser smoke failed: {exc}") from exc

        if console_errors or page_errors or failed_responses or failed_requests:
            details = "; ".join(
                (console_errors + page_errors + failed_responses + failed_requests)[:20]
            )
            raise DeployExecutionError(
                "browser reported console, page, or request errors: " + details
            )
        return {
            "status": "passed",
            "routes": [route.path for route in representative],
            "routes_by_viewport": checked_by_viewport,
            "viewports": ["1440x1000", "390x844"],
            "screenshots": [
                str(screenshots / f"{name}-desktop.png"),
                str(screenshots / f"{name}-mobile.png"),
            ],
        }

    @contextmanager
    def _preview_server(self, site: Path, log: Path) -> Iterator[str]:
        ready_file = log.with_suffix(".ready.json")
        environment = dict(os.environ)
        environment.update(
            {
                "REASBOOK_SITE_DIR": str(site),
                "REASBOOK_DOC_SOURCE": str(site / "docs"),
                "REASBOOK_SITE_ROOT": self.spec.base_path,
                "PYTHONUNBUFFERED": "1",
            }
        )
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("w", encoding="utf-8") as output:
            process = subprocess.Popen(
                (
                    sys.executable,
                    str(self.preview_script),
                    "0",
                    "--host",
                    "127.0.0.1",
                    "--site-root",
                    self.spec.base_path,
                    "--public-prefix",
                    "",
                    "--routing-mode",
                    _PRODUCTION_ROUTING_MODE,
                    "--ready-file",
                    str(ready_file),
                ),
                cwd=self.repo_root,
                env=environment,
                stdout=output,
                stderr=subprocess.STDOUT,
                text=True,
            )
            try:
                origin = self._wait_for_server(process, ready_file)
                yield origin
            finally:
                if process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=5.0)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait(timeout=5.0)

    def _wait_for_server(
        self,
        process: subprocess.Popen,
        ready_file: Path,
    ) -> str:
        deadline = time.monotonic() + 15.0
        last_error: Exception | None = None
        while time.monotonic() < deadline:
            returncode = process.poll()
            if returncode is not None:
                raise DeployExecutionError(
                    f"preview server exited early with status {returncode}"
                )
            try:
                ready = json.loads(ready_file.read_text(encoding="utf-8"))
                if not isinstance(ready, dict) or not isinstance(
                    ready.get("origin"), str
                ):
                    raise DeployExecutionError(
                        "preview readiness file has an invalid payload"
                    )
                origin = ready["origin"]
                parsed = urlsplit(origin)
                if (
                    parsed.scheme != "http"
                    or parsed.hostname != "127.0.0.1"
                    or parsed.port is None
                    or parsed.path
                    or parsed.query
                    or parsed.fragment
                ):
                    raise DeployExecutionError(
                        "preview readiness file has an unsafe origin"
                    )
                health_url = origin + self.spec.base_path + "release-spec.json"
                self._read_json(health_url)
                return origin
            except (
                DeployExecutionError,
                OSError,
                URLError,
                HTTPError,
                ValueError,
                json.JSONDecodeError,
            ) as exc:
                last_error = exc
                time.sleep(0.1)
        raise DeployExecutionError(f"preview server did not become ready: {last_error}")

    @staticmethod
    def _read_json(url: str) -> dict[str, Any]:
        try:
            with urlopen(
                Request(url, headers={"User-Agent": "ReasBook-E2E/1"}),
                timeout=10.0,
            ) as response:
                if response.status != 200:
                    raise DeployExecutionError(
                        f"health endpoint returned HTTP {response.status}"
                    )
                value = json.loads(response.read().decode("utf-8"))
        except (
            OSError,
            URLError,
            HTTPError,
            UnicodeError,
            json.JSONDecodeError,
        ) as exc:
            raise DeployExecutionError(
                f"cannot read preview health endpoint: {exc}"
            ) from exc
        if not isinstance(value, dict):
            raise DeployExecutionError("preview health endpoint is not a JSON object")
        return value

    def _new_run_root(self) -> Path:
        validation = self.layout.cache_root / "validation"
        if validation.is_symlink():
            raise DeployExecutionError(
                f"release validation root must not be a symlink: {validation}"
            )
        validation.mkdir(parents=True, exist_ok=True)
        release_root = validation / self.spec.release_id
        if release_root.is_symlink():
            raise DeployExecutionError(
                f"release validation directory must not be a symlink: {release_root}"
            )
        release_root.mkdir(exist_ok=True)
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        run_root = release_root / f"{timestamp}-{uuid.uuid4().hex[:8]}"
        run_root.mkdir()
        return run_root

    @staticmethod
    def _remove_scratch(run_root: Path, scratch: Path) -> None:
        resolved_run = run_root.resolve()
        resolved_scratch = scratch.resolve()
        if resolved_scratch.parent != resolved_run or scratch.name != "scratch":
            raise DeployExecutionError(
                f"refusing unsafe validation cleanup target: {scratch}"
            )
        shutil.rmtree(scratch)

    def _write_result(self, run_root: Path, value: dict[str, Any]) -> None:
        atomic_write_json(run_root / "result.json", value)
        atomic_write_json(run_root.parent / "latest.json", value)


__all__ = ["ReleaseAcceptanceRunner"]
