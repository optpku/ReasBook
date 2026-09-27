"""Assemble canonical and versioned branch artifacts into one static site."""

from __future__ import annotations

import html
import json
import os
from pathlib import Path
import shutil
import uuid

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandRunner,
    atomic_write_json,
)

from ..errors import DeployExecutionError
from ..git import version_key
from .models import ProjectSpec, ReleaseSpec
from .results import BranchBuildResult, ReleaseBuildReport
from .store import ReleaseLayout


class ReleaseSiteAssembler:
    """Normalize branch layouts while enforcing explicit canonical versions."""

    def __init__(
        self,
        tooling_root: Path,
        layout: ReleaseLayout,
    ) -> None:
        self.tooling_root = Path(tooling_root).expanduser().resolve()
        self.layout = layout

    def assemble(
        self,
        spec: ReleaseSpec,
        report: ReleaseBuildReport,
    ) -> Path:
        if report.status == "failed":
            raise DeployExecutionError("cannot assemble a failed release build")
        by_branch = {result.branch: result for result in report.branches}
        self._require_canonical_branches(spec, by_branch)

        workspace = self.layout.root / f".assemble-{uuid.uuid4().hex}"
        monolith = workspace / ".artifacts" / "monolith"
        output = workspace / ".site"
        monolith.mkdir(parents=True)
        try:
            for branch in sorted(
                spec.branches, key=lambda item: version_key(item.name)
            ):
                result = by_branch.get(branch.name)
                if result is None or not result.succeeded or result.site_root is None:
                    continue
                self._overlay(Path(result.site_root), monolith)
            for project in spec.canonical_projects():
                result = by_branch[project.branch]
                if result.site_root is None:
                    raise DeployExecutionError(
                        f"canonical project has no site: {project.key}"
                    )
                self._replace_canonical_project(
                    monolith,
                    Path(result.site_root),
                    project,
                )
            if spec.include_historical_versions:
                self._copy_versions(spec, by_branch, monolith)
                self._write_versions_index(spec, by_branch, monolith)
            self._run_repository_assembler(spec, workspace)
            atomic_write_json(output / "release-spec.json", spec.public_dict())
            self._publish(output)
            return self.layout.site
        finally:
            shutil.rmtree(workspace, ignore_errors=True)

    @staticmethod
    def _require_canonical_branches(
        spec: ReleaseSpec,
        by_branch: dict[str, BranchBuildResult],
    ) -> None:
        for project in spec.canonical_projects():
            result = by_branch.get(project.branch)
            if result is None or not result.succeeded or not result.site_root:
                raise DeployExecutionError(
                    f"canonical project {project.key} has no successful "
                    f"site on {project.branch}"
                )

    def _run_repository_assembler(
        self,
        spec: ReleaseSpec,
        workspace: Path,
    ) -> None:
        projects = [
            {
                "kind": project.kind,
                "kindTitle": "Books" if project.kind == "books" else "Papers",
                "name": project.project_id,
                "slug": project.slug,
                "branch": project.branch,
            }
            for project in spec.canonical_projects()
        ]
        env = {
            "PROJECTS_JSON": json.dumps(projects, separators=(",", ":")),
            "REASBOOK_REQUIRE_DOCS": "1" if spec.policy.require_docs else "0",
            "REASBOOK_REQUIRE_THEOREM_MAPS": (
                "1" if spec.policy.theorem_graph != "none" else "0"
            ),
            "REASBOOK_SITE_ROOT": spec.base_path,
        }
        self._run(
            (
                str(self.tooling_root / "sdk" / "common" / "bin" / "python"),
                str(self.tooling_root / "scripts" / "pages" / "assemble.py"),
            ),
            workspace,
            env,
            "assemble-pages.log",
        )
        self._run(
            (
                str(
                    self.tooling_root
                    / "sdk"
                    / "theorem_graph"
                    / "bin"
                    / "theorem-graph"
                ),
                "catalog",
                "--site-root",
                str(workspace / ".site"),
            ),
            workspace,
            {},
            "theorem-catalog.log",
        )
        self._run(
            (
                str(self.tooling_root / "sdk" / "common" / "bin" / "python"),
                str(self.tooling_root / "scripts" / "pages" / "reader_entrypoints.py"),
                str(workspace / ".site"),
            ),
            workspace,
            {},
            "reader-entrypoints.log",
        )
        self._run(
            (
                str(self.tooling_root / "sdk" / "common" / "bin" / "python"),
                str(self.tooling_root / "scripts" / "pages" / "verify.py"),
            ),
            workspace,
            env,
            "verify-pages.log",
        )

    def _run(
        self,
        argv: tuple[str, ...],
        cwd: Path,
        env: dict[str, str],
        log_name: str,
    ) -> None:
        log = self.layout.logs / "assembly" / log_name
        runner = CommandRunner(output_file=log)
        try:
            result = runner.run(Command(argv, cwd=cwd, env=env, timeout=1800.0))
        except CommandExecutionError as exc:
            raise DeployExecutionError(
                f"cannot execute site assembly command; log: {log}: {exc}"
            ) from exc
        if result.returncode != 0:
            raise DeployExecutionError(
                f"site assembly command failed ({result.returncode}); log: {log}"
            )

    @classmethod
    def _overlay(cls, source: Path, destination: Path) -> None:
        cls._validate_tree(source)
        shutil.copytree(source, destination, dirs_exist_ok=True)

    @classmethod
    def _replace_canonical_project(
        cls,
        monolith: Path,
        branch_site: Path,
        project: ProjectSpec,
    ) -> None:
        kind_title = "Books" if project.kind == "books" else "Papers"
        candidates = (
            Path(project.kind) / project.slug,
            Path(project.slug),
            Path("docs") / "ReasBook" / kind_title / project.project_id,
            Path("docs") / "ReasBook" / project.project_id,
            Path("docs") / kind_title / project.project_id,
            Path("docs") / project.project_id,
            Path("docs") / "ReasBook" / f"{project.project_id}.html",
            Path("docs") / f"{project.project_id}.html",
            Path("theorem-maps") / project.kind / project.slug,
        )
        for relative in candidates:
            target = monolith / relative
            if target.is_symlink() or target.is_file():
                target.unlink(missing_ok=True)
            elif target.is_dir():
                shutil.rmtree(target)
            source = branch_site / relative
            if source.is_dir():
                cls._validate_tree(source)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copytree(source, target)
            elif source.is_file():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)

    @classmethod
    def _copy_versions(
        cls,
        spec: ReleaseSpec,
        by_branch: dict[str, BranchBuildResult],
        output: Path,
    ) -> None:
        versions = output / "versions"
        versions.mkdir(parents=True, exist_ok=True)
        for branch in spec.branches:
            result = by_branch.get(branch.name)
            if result is None or not result.succeeded or not result.site_root:
                continue
            source = Path(result.site_root)
            cls._validate_tree(source)
            shutil.copytree(source, versions / branch.name)

    @staticmethod
    def _write_versions_index(
        spec: ReleaseSpec,
        by_branch: dict[str, BranchBuildResult],
        output: Path,
    ) -> None:
        links = []
        for branch in sorted(spec.branches, key=lambda item: version_key(item.name)):
            result = by_branch.get(branch.name)
            if result is not None and result.succeeded and result.site_root:
                links.append(
                    "\n".join(
                        [
                            "      <li>",
                            f'        <a class="resource-link" href="./{html.escape(branch.name, quote=True)}/">',
                            f'          <span translate="no">{html.escape(branch.name)}</span>',
                            '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                            "        </a>",
                            "      </li>",
                        ]
                    )
                )
        content = "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                '  <meta name="theme-color" content="#17211c" />',
                "  <title>ReasBook Versions</title>",
                '  <link rel="stylesheet" href="../static/catalog.css" />',
                "</head>",
                "<body>",
                '  <a class="skip-link" href="#main-content">Skip to content</a>',
                '  <header class="masthead">',
                '    <div class="masthead-inner">',
                '      <a class="brand" href="../">',
                '        <span class="proof-mark" aria-hidden="true">&#8866;</span>',
                "        <span><strong>ReasBook</strong><small>Formal Mathematics Library</small></span>",
                "      </a>",
                "    </div>",
                "  </header>",
                '  <main id="main-content" class="page-shell narrow-shell">',
                '    <section class="page-heading">',
                '      <p class="eyebrow">Release Archive</p>',
                "      <h1>Versions</h1>",
                "    </section>",
                '    <ul class="resource-list" role="list">',
                *links,
                "    </ul>",
                '    <a class="back-link" href="../"><span aria-hidden="true">&#8592;</span> Back to ReasBook</a>',
                "  </main>",
                "</body>",
                "</html>",
                "",
            ]
        )
        (output / "versions" / "index.html").write_text(content, encoding="utf-8")

    @staticmethod
    def _validate_tree(root: Path) -> None:
        if not root.is_dir() or root.is_symlink():
            raise DeployExecutionError(f"site tree is not a directory: {root}")
        symlink = next((path for path in root.rglob("*") if path.is_symlink()), None)
        if symlink is not None:
            raise DeployExecutionError(f"site tree contains a symlink: {symlink}")

    def _publish(self, staged: Path) -> None:
        target = self.layout.site
        if target.parent.is_symlink():
            raise DeployExecutionError(f"release site parent is a symlink: {target.parent}")
        target.parent.mkdir(parents=True, exist_ok=True)
        backup = target.parent / f".site-backup-{uuid.uuid4().hex}"
        # ``Path.exists`` is false for a broken symlink.  Include symlinks and
        # regular-file remnants so an interrupted/corrupted publish is still
        # moved out of the way and can be restored if the rename fails.
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
            if backup.is_symlink() or backup.is_file():
                backup.unlink(missing_ok=True)
            elif backup.is_dir():
                shutil.rmtree(backup)


__all__ = ["ReleaseSiteAssembler"]
