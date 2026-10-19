"""Declaration environment adapters used by the theorem graph builder."""

from __future__ import annotations

import json
import os
import shutil
import tempfile
from pathlib import Path
from typing import Any, Callable, Mapping, Protocol, Sequence

from reasbook_sdk_common import (
    Command as SharedCommand,
    CommandTimeoutError,
    CommandRunner as SharedRunner,
    atomic_write_json,
)

from .analysis import fallback_raw_declarations
from .errors import ExtractionError
from .models import Project


class DeclarationExtractor(Protocol):
    """Protocol for a source of declaration metadata."""

    def extract(
        self, repo_root: Path, projects: Sequence[Project]
    ) -> Mapping[str, list[dict[str, Any]]]:
        """Return raw declarations keyed by project id."""


class SourceExtractor:
    """Always use source comments as a deterministic offline fallback."""

    def extract(
        self, repo_root: Path, projects: Sequence[Project]
    ) -> Mapping[str, list[dict[str, Any]]]:
        return {
            project.project_id: fallback_raw_declarations(project)
            for project in projects
        }


Runner = Callable[..., Any]


class LeanEnvironmentExtractor:
    """Run a repository-provided Lean extractor without editing source files.

    The extractor receives a temporary JSON config and writes a temporary JSON
    result. A custom runner may be injected for tests or another process
    supervisor. It may implement the shared ``run(Command)`` contract or the
    familiar ``subprocess.run``-compatible callable shape.

    Projects are deliberately exported one at a time. Each project therefore
    gets a fresh Lean process and environment instead of accumulating every
    book in one high-memory import.
    """

    def __init__(
        self,
        extractor: Path,
        *,
        lake_bin: str | None = None,
        command_prefix: Sequence[str] = (),
        timeout_seconds: float | None = 1800.0,
        runner: Runner | None = None,
    ) -> None:
        self.extractor = Path(extractor).expanduser().resolve()
        self.lake_bin = (
            lake_bin or os.environ.get("LAKE_BIN") or shutil.which("lake") or "lake"
        )
        self.command_prefix = tuple(command_prefix)
        self.timeout_seconds = timeout_seconds
        self.runner = runner
        self._shared_runner = None if runner is not None else SharedRunner()

    def command(self, config_path: Path, output_path: Path) -> tuple[str, ...]:
        return (
            *self.command_prefix,
            self.lake_bin,
            "env",
            "lean",
            "--run",
            str(self.extractor),
            str(config_path),
            str(output_path),
        )

    def extract(
        self, repo_root: Path, projects: Sequence[Project]
    ) -> Mapping[str, list[dict[str, Any]]]:
        """Export projects serially, with one Lean process per project."""

        extracted: dict[str, list[dict[str, Any]]] = {}
        for project in projects:
            if not project.root_module:
                continue
            extracted.update(self.extract_project(repo_root, project))
        return extracted

    def extract_project(
        self, repo_root: Path, project: Project
    ) -> Mapping[str, list[dict[str, Any]]]:
        """Export exactly one compiled project in an isolated Lean process."""

        if not self.extractor.is_file():
            raise ExtractionError(f"Lean extractor does not exist: {self.extractor}")
        if not project.root_module:
            return {}
        config = {
            "projects": [{"id": project.project_id, "rootModule": project.root_module,
                          "rootModules": []}]
        }
        repo_root = Path(repo_root).expanduser().resolve()
        working_dir = repo_root / "ReasBook"
        if not working_dir.is_dir():
            working_dir = repo_root
        try:
            with tempfile.TemporaryDirectory(prefix="theorem-graph-") as temp:
                temp_root = Path(temp)
                config_path = temp_root / "config.json"
                output_path = temp_root / "raw.json"
                atomic_write_json(config_path, config)
                command = self.command(config_path, output_path)
                try:
                    if self._shared_runner is not None:
                        result = self._shared_runner.run(
                            SharedCommand(
                                command, cwd=working_dir, timeout=self.timeout_seconds
                            )
                        )
                    else:
                        if self.runner is None:
                            raise ExtractionError(
                                "an extractor runner is not configured"
                            )
                        if hasattr(self.runner, "run"):
                            result = self.runner.run(  # type: ignore[attr-defined]
                                SharedCommand(
                                    command,
                                    cwd=working_dir,
                                    timeout=self.timeout_seconds,
                                )
                            )
                        else:
                            result = self.runner(
                                command,
                                cwd=working_dir,
                                check=False,
                                capture_output=True,
                                text=True,
                                timeout=self.timeout_seconds,
                            )
                except CommandTimeoutError as exc:
                    raise ExtractionError(str(exc)) from exc
                except Exception as exc:
                    raise ExtractionError(
                        f"could not execute Lean extractor: {exc}"
                    ) from exc
                return_code = getattr(result, "returncode", 0)
                if return_code != 0:
                    stderr = str(getattr(result, "stderr", "") or "").strip()
                    message = f"Lean environment export failed ({return_code})"
                    if stderr:
                        message += f": {stderr}"
                    raise ExtractionError(message)
                if not output_path.is_file():
                    raise ExtractionError(
                        f"Lean extractor completed without output: {output_path}"
                    )
                try:
                    payload = json.loads(output_path.read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError) as exc:
                    raise ExtractionError(
                        f"invalid Lean extractor output: {exc}"
                    ) from exc
        except ExtractionError:
            raise
        except OSError as exc:
            raise ExtractionError(f"could not prepare Lean extractor: {exc}") from exc
        if not isinstance(payload, list):
            raise ExtractionError("Lean extractor output must be a JSON array")
        result: dict[str, list[dict[str, Any]]] = {}
        for item in payload:
            if not isinstance(item, Mapping):
                continue
            project_id = str(item.get("id") or "")
            declarations = item.get("declarations") or []
            if not isinstance(declarations, list):
                raise ExtractionError(
                    f"declarations for {project_id or '<unknown>'} must be an array"
                )
            result[project_id] = [
                dict(declaration)
                for declaration in declarations
                if isinstance(declaration, Mapping)
            ]
        return result


__all__ = [
    "DeclarationExtractor",
    "LeanEnvironmentExtractor",
    "SourceExtractor",
]
