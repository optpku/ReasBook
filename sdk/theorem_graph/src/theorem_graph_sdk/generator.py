"""End-to-end theorem graph generation with atomic output publication."""

from __future__ import annotations

import os
import math
import shutil
import subprocess
import time
import re
import tempfile
import uuid
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from .analysis import build_data, project_title
from .errors import ExtractionError, GraphConfigError, GraphRenderError
from .extractor import DeclarationExtractor, LeanEnvironmentExtractor, SourceExtractor
from .models import GenerationReport, Project
from .projects import discover_projects, generic_projects, has_curated_map
from .render import copy_curated_map, copy_generic_map, curated_counts, write_catalog


RESOURCE_ROOT = Path(__file__).with_name("resources")


@dataclass(frozen=True)
class TheoremGraphConfig:
    """Inputs for one graph generation run."""

    repo_root: Path
    site_root: Path
    branch: str
    repository: str = "https://github.com/optpku/ReasBook"
    assets: Path | None = None
    extractor: Path | None = None
    source_root: Path | None = None
    compiled_root: Path | None = None
    lake_bin: str | None = None
    commit: str | None = None
    extractor_timeout_seconds: float | None = 1800.0
    include_generic: bool = False
    fallback_to_source: bool = True
    replace_output: bool = True
    project_keys: tuple[str, ...] = ()
    source_only: bool = False

    def resolved(self) -> "TheoremGraphConfig":
        repo_root = Path(self.repo_root).expanduser().resolve()
        site_root = Path(self.site_root).expanduser()
        if not site_root.is_absolute():
            site_root = repo_root / site_root
        source_root = Path(self.source_root).expanduser() if self.source_root else None
        if source_root is not None and not source_root.is_absolute():
            source_root = repo_root / source_root
        assets = (
            Path(self.assets).expanduser()
            if self.assets
            else RESOURCE_ROOT / "assets"
        )
        if assets is not None and not assets.is_absolute():
            assets = repo_root / assets
        extractor = (
            Path(self.extractor).expanduser()
            if self.extractor
            else RESOURCE_ROOT / "Extract.lean"
        )
        if extractor is not None and not extractor.is_absolute():
            extractor = repo_root / extractor
        compiled_root = (
            Path(self.compiled_root).expanduser() if self.compiled_root else None
        )
        if compiled_root is not None and not compiled_root.is_absolute():
            compiled_root = repo_root / compiled_root
        branch = self.branch.strip()
        if not branch:
            raise GraphConfigError("branch must be non-empty")
        if any(char in branch for char in "\x00\r\n"):
            raise GraphConfigError("branch contains a control character")
        if any(char in self.repository for char in "\x00\r\n"):
            raise GraphConfigError("repository contains a control character")
        project_keys = tuple(sorted(set(self.project_keys)))
        for key in project_keys:
            if not re.fullmatch(
                r"(?:books|papers)/[A-Za-z0-9][A-Za-z0-9_.-]*", key
            ):
                raise GraphConfigError(f"invalid project key: {key!r}")
        if self.extractor_timeout_seconds is not None and (
            not math.isfinite(self.extractor_timeout_seconds)
            or self.extractor_timeout_seconds <= 0
        ):
            raise GraphConfigError("extractor_timeout_seconds must be positive")
        return TheoremGraphConfig(
            repo_root=repo_root,
            site_root=site_root.resolve(),
            branch=branch,
            repository=self.repository.rstrip("/"),
            assets=assets.resolve() if assets else None,
            extractor=extractor.resolve() if extractor else None,
            source_root=source_root.resolve() if source_root else None,
            compiled_root=compiled_root.resolve() if compiled_root else None,
            lake_bin=self.lake_bin,
            commit=self.commit,
            extractor_timeout_seconds=self.extractor_timeout_seconds,
            include_generic=self.include_generic,
            fallback_to_source=self.fallback_to_source,
            replace_output=self.replace_output,
            project_keys=project_keys,
            source_only=self.source_only,
        )


CommitReader = Callable[[Path], str]


def read_git_commit(repo_root: Path) -> str:
    """Read the current commit, returning an empty value outside a checkout."""

    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError:
        return ""
    return result.stdout.strip() if result.returncode == 0 else ""


class GraphGenerator:
    """Discover projects, build graph payloads, and publish them atomically."""

    def __init__(
        self,
        config: TheoremGraphConfig,
        *,
        extractor: DeclarationExtractor | None = None,
        project_discoverer: Callable[..., list[Project]] = discover_projects,
        commit_reader: CommitReader = read_git_commit,
        progress: Callable[[Mapping[str, Any]], None] | None = None,
    ) -> None:
        self.config = config.resolved()
        self.extractor = extractor
        self.project_discoverer = project_discoverer
        self.commit_reader = commit_reader
        self.progress = progress
        self._source_fallback_ids: set[str] = set()
        self._source_fallback_reasons: dict[str, str] = {}

    def _progress(self, phase: str, project: Project | None = None, **details: Any) -> None:
        if self.progress is not None:
            event = {"phase": phase, **details}
            if project is not None:
                event["project"] = f"{project.kind}/{project.project_id}"
            self.progress(event)

    def discover(self) -> list[Project]:
        projects = self.project_discoverer(
            self.config.repo_root,
            source_root=self.config.source_root,
            compiled_root=self.config.compiled_root,
        )
        if not self.config.project_keys:
            return projects
        selected = set(self.config.project_keys)
        return [
            project
            for project in projects
            if f"{project.kind}/{project.project_id}" in selected
        ]

    def _extract(
        self, projects: Sequence[Project]
    ) -> Mapping[str, list[dict[str, Any]]]:
        targets = generic_projects(list(projects), self.config.include_generic)
        if not targets:
            return {}
        extractor = self.extractor
        if self.config.source_only:
            extractor = SourceExtractor()
            # ``build_data`` uses ``root_module`` to select the evidence label.
            # A source-only run can still discover a stale/available compiled
            # root, so mark these projects explicitly to prevent reporting
            # source comments as a Lean-environment extraction.
            self._source_fallback_ids.update(
                project.project_id for project in targets
            )
            self._source_fallback_reasons.update(
                {project.project_id: "source-only" for project in targets}
            )
        elif extractor is None:
            if self.config.extractor is not None:
                extractor = LeanEnvironmentExtractor(
                    self.config.extractor,
                    lake_bin=self.config.lake_bin,
                    timeout_seconds=self.config.extractor_timeout_seconds,
                )
            else:
                extractor = SourceExtractor()
        extracted: dict[str, list[dict[str, Any]]]
        if isinstance(extractor, LeanEnvironmentExtractor):
            extracted = {}
            for project in targets:
                started = time.monotonic()
                self._progress("extract-start", project)
                if not project.root_module:
                    self._source_fallback_reasons[project.project_id] = (
                        "compiled-root-unavailable"
                    )
                    self._progress("extract-source-fallback", project, reason="compiled-root-unavailable")
                    continue
                try:
                    project_result = extractor.extract_project(
                        self.config.repo_root, project
                    )
                except ExtractionError:
                    if not self.config.fallback_to_source:
                        raise
                    self._source_fallback_ids.add(project.project_id)
                    self._source_fallback_reasons[project.project_id] = (
                        "compiled-extraction-failed"
                    )
                    self._progress("extract-source-fallback", project,
                                   reason="compiled-extraction-failed",
                                   elapsed_seconds=round(time.monotonic() - started, 3))
                    continue
                declarations = project_result.get(project.project_id)
                if declarations is not None:
                    extracted[project.project_id] = declarations
                self._progress("extract-complete", project,
                               declarations=len(declarations or []),
                               elapsed_seconds=round(time.monotonic() - started, 3))
        else:
            try:
                extracted = dict(extractor.extract(self.config.repo_root, targets))
            except ExtractionError:
                if not self.config.fallback_to_source or isinstance(
                    extractor, SourceExtractor
                ):
                    raise
                extracted = {}
                self._source_fallback_ids.update(
                    project.project_id for project in targets
                )
                self._source_fallback_reasons.update(
                    {
                        project.project_id: "compiled-extraction-failed"
                        for project in targets
                    }
                )
        missing = [
            project for project in targets if project.project_id not in extracted
        ]
        if missing and not self.config.fallback_to_source:
            project_ids = ", ".join(project.project_id for project in missing)
            raise ExtractionError(
                f"compiled extraction returned no data for: {project_ids}"
            )
        if self.config.fallback_to_source:
            if missing:
                fallback = SourceExtractor().extract(self.config.repo_root, missing)
                for project in missing:
                    extracted[project.project_id] = fallback.get(project.project_id, [])
                    self._source_fallback_ids.add(project.project_id)
                    self._source_fallback_reasons.setdefault(
                        project.project_id,
                        "compiled-result-missing"
                        if project.root_module
                        else "compiled-root-unavailable",
                    )
        return extracted

    def _render_tree(
        self,
        projects: Sequence[Project],
        raw_by_project: Mapping[str, list[dict[str, Any]]],
        source_inventory_by_project: Mapping[str, list[dict[str, Any]]],
        destination: Path,
    ) -> list[dict[str, Any]]:
        commit = self.config.commit
        if commit is None:
            commit = self.commit_reader(self.config.repo_root)

        def entry_base(project: Project) -> dict[str, Any]:
            return {
                "id": project.project_id,
                "title": project_title(project),
                "kind": project.kind,
                "slug": project.slug,
                "branch": self.config.branch,
            }

        entries: list[dict[str, Any]] = []
        for project in projects:
            self._progress("render-start", project)
            output = destination / project.kind / project.slug
            curated_static = project.root / "theorem-map"
            if has_curated_map(project):
                copy_curated_map(
                    curated_static,
                    output,
                    project={
                        "id": project.project_id,
                        "title": project_title(project),
                        "kind": project.kind,
                        "branch": self.config.branch,
                        "commit": commit,
                        "repository": self.config.repository,
                        "sourceRoot": project.source_root,
                    },
                )
                nodes, edges = curated_counts(curated_static)
                mode = "curated"
            elif self.config.include_generic:
                raw = raw_by_project.get(project.project_id, [])
                graph_project = (
                    replace(project, root_module=None)
                    if project.project_id in self._source_fallback_ids
                    else project
                )
                data = build_data(
                    graph_project,
                    raw,
                    repository=self.config.repository,
                    branch=self.config.branch,
                    commit=commit,
                    source_inventory_raw=source_inventory_by_project.get(
                        project.project_id
                    ),
                )
                fallback_reason = self._source_fallback_reasons.get(project.project_id)
                if fallback_reason:
                    generation = dict(data.get("generation") or {})
                    generation["fallbackReason"] = fallback_reason
                    data["generation"] = generation
                if self.config.assets is None:
                    raise GraphRenderError(
                        "assets are required when generating a generic theorem map"
                    )
                copy_generic_map(self.config.assets, output, data)
                nodes = len(data.get("items") or [])
                edges = sum(
                    len(item.get("dependencies") or [])
                    for item in data.get("items") or []
                )
                mode = "generated"
            else:
                entry = entry_base(project)
                entry.update({"nodes": 0, "edges": 0, "mode": "skipped"})
                entries.append(entry)
                continue
            entry = entry_base(project)
            entry.update({"nodes": nodes, "edges": edges, "mode": mode})
            entries.append(entry)
            self._progress("render-complete", project, nodes=nodes, edges=edges)
        return entries

    @staticmethod
    def _remove_path(path: Path) -> None:
        """Remove a staged or published entry without following symlinks."""

        if path.is_symlink() or path.is_file():
            path.unlink(missing_ok=True)
        elif path.is_dir():
            shutil.rmtree(path)

    def _preserve_unmanaged_output(self, target: Path, staged: Path) -> None:
        """Copy non-project entries for the opt-in merge mode.

        The generated books/papers trees and catalog are managed by this SDK
        and are always rebuilt. Other top-level files are retained when
        replace_output is false so callers can keep local annotations.
        """

        if not target.is_dir() or target.is_symlink():
            return
        managed = {"books", "papers", "index.html"}
        for child in target.iterdir():
            if child.name in managed or child.name.startswith(".theorem-maps-"):
                continue
            destination = staged / child.name
            if child.is_symlink():
                destination.symlink_to(os.readlink(child))
            elif child.is_dir():
                shutil.copytree(child, destination, symlinks=True)
            else:
                shutil.copy2(child, destination)

    def _publish(self, staged: Path, parent: Path) -> Path:
        """Atomically publish a complete theorem-maps tree.

        A failed rename restores the previous tree. replace_output=false
        retains unrelated top-level files, while generated project directories
        are synchronized and stale ones are removed.
        """

        target = parent / "theorem-maps"
        if not self.config.replace_output:
            self._preserve_unmanaged_output(target, staged)
        backup = parent / f".theorem-maps-backup-{uuid.uuid4().hex}"
        had_target = target.exists() or target.is_symlink()
        if had_target:
            os.replace(target, backup)
        try:
            os.replace(staged, target)
        except OSError as exc:
            if had_target and not (target.exists() or target.is_symlink()):
                os.replace(backup, target)
            raise GraphRenderError(f"could not publish theorem maps: {exc}") from exc
        if had_target:
            self._remove_path(backup)
        return target

    def generate(self) -> GenerationReport:
        """Generate all configured maps and atomically replace theorem-maps/."""

        self._source_fallback_ids.clear()
        self._source_fallback_reasons.clear()
        projects = self.discover()
        self._progress("discovered", projects=len(projects))
        self.config.site_root.mkdir(parents=True, exist_ok=True)
        parent = self.config.site_root
        temporary = Path(tempfile.mkdtemp(prefix=".theorem-maps-stage-", dir=parent))
        staged_maps = temporary / "theorem-maps"
        staged_maps.mkdir(parents=True, exist_ok=True)
        try:
            raw_by_project = self._extract(projects)
            generic = generic_projects(list(projects), self.config.include_generic)
            compiled_projects = [
                project
                for project in generic
                if project.root_module
                and project.project_id in raw_by_project
                and project.project_id not in self._source_fallback_ids
            ]
            source_inventory_by_project: dict[str, list[dict[str, Any]]] = {}
            for project in compiled_projects:
                started = time.monotonic()
                self._progress("source-inventory-start", project)
                source_inventory_by_project.update(
                    SourceExtractor().extract(self.config.repo_root, [project]))
                self._progress("source-inventory-complete", project,
                               elapsed_seconds=round(time.monotonic() - started, 3))
            entries = self._render_tree(
                projects,
                raw_by_project,
                source_inventory_by_project,
                staged_maps,
            )
            # Branch artifacts retain the historical four-column catalog;
            # the post-merge catalog renderer adds the branch column.
            write_catalog(temporary, entries, include_branch=False)
            self._publish(staged_maps, parent)
            self._progress("published", projects=len(entries))
            generated = sum(entry["mode"] != "skipped" for entry in entries)
            skipped = len(entries) - generated
            return GenerationReport(
                project_count=len(projects),
                generated_count=generated,
                skipped_count=skipped,
                output_root=parent / "theorem-maps",
                entries=tuple(entries),
            )
        finally:
            shutil.rmtree(temporary, ignore_errors=True)


__all__ = [
    "GraphGenerator",
    "TheoremGraphConfig",
    "read_git_commit",
]
