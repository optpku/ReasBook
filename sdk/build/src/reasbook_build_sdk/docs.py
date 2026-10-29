"""Bounded-memory API documentation builds for selected ReasBook roots."""

from __future__ import annotations

from contextlib import closing, contextmanager
from dataclasses import dataclass
import fcntl
import hashlib
from html import unescape as html_unescape
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import platform
import re
import shutil
import sqlite3
import stat
import tempfile
from typing import Iterator, Literal, Protocol
from urllib.parse import quote, unquote, urljoin, urlsplit
import uuid

from .command import Command, CommandResult
from .errors import BuildFailed, ConfigurationError
from .executor import SubprocessRunner
from .project import discover_project
from . import statement_docs
from .targets import parse_library_declarations


_MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:[.][A-Za-z_][A-Za-z0-9_']*)*$")
_GITHUB_SEGMENT_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
_IMPORT_RE = re.compile(r"^[ \t]*(?:public[ \t]+)?import[ \t]+(.+?)\s*$")
_PROFILE = "project-modules-v2"
_MODULE_BATCH_SIZE = 128
_LINK_POLICY = {
    "schema_version": 1,
    "project_source_links": "unique-reachable-source-to-immutable-commit",
    "missing_html": "explicit-stub",
    "missing_non_html": "reject",
}
_ANALYSIS_PROFILE = "project-docs-analysis-v1"
_HTML_SPACE = " \t\n\r\f"
_COMPILED_ARTIFACT_SUFFIXES = frozenset({".a", ".olean", ".so"})
_ANALYZER_REQUIRED_TABLES = frozenset(
    {
        "axioms",
        "class_inductives",
        "constructors",
        "declaration_args",
        "declaration_attrs",
        "declaration_markdown_docstrings",
        "declaration_ranges",
        "declaration_verso_docstrings",
        "definition_equations",
        "definitions",
        "inductives",
        "instance_args",
        "instances",
        "internal_names",
        "module_docs_markdown",
        "module_imports",
        "modules",
        "name_info",
        "opaques",
        "schema_meta",
        "structure_constructors",
        "structure_field_args",
        "structure_fields",
        "structure_parents",
        "structures",
        "tactic_tags",
        "tactics",
    }
)
_ANALYZER_SCHEMA_META_KEYS = frozenset({"ddl_hash", "type_hash"})
_WINDOWS_ABSOLUTE_RE = re.compile(r"^[A-Za-z]:[/\\]")
_MANAGED_CACHE_METADATA_KEYS = frozenset(
    {
        "schema",
        "branch",
        "commit",
        "manifest_sha256",
        "toolchain",
        "architecture",
    }
)
_FINALIZER_METADATA_KEYS = frozenset(
    {
        "schema",
        "purpose",
        "workspace_policy",
        "branch",
        "commit",
        "manifest_sha256",
        "toolchain",
        "architecture",
        "tooling_sha256",
        "seed_namespace",
    }
)
_CONFIGURED_FINALIZER_METADATA_KEYS = _FINALIZER_METADATA_KEYS | frozenset(
    {"build_configuration", "build_configuration_sha256"}
)
_PROJECT_FINALIZER_METADATA_KEYS = _CONFIGURED_FINALIZER_METADATA_KEYS | frozenset(
    {"project_key"}
)
_FINALIZER_BUILD_CONFIGURATION_KEYS = frozenset(
    {"schema", "lean_threads", "lake_threads"}
)
_MAX_MANAGED_CACHE_METADATA_BYTES = 1024 * 1024
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_BRANCH_RE = re.compile(r"^[A-Za-z0-9._/-]+$")


class _Runner(Protocol):
    def run(self, command: Command) -> CommandResult:
        """Run one documentation command."""


@dataclass(frozen=True)
class _ManagedCacheIdentity:
    value: dict[str, object]
    dependency_artifacts_are_immutable: bool


@dataclass(frozen=True)
class _HtmlReference:
    value: str
    start: int
    end: int


@dataclass(frozen=True)
class _StartTagAttribute:
    name: str
    value: str | None
    start: int | None
    end: int | None


class _LinkParser(HTMLParser):
    """Collect link values and their exact source spans in start tags."""

    def __init__(self, source: str) -> None:
        super().__init__(convert_charrefs=True)
        self.base_href: str | None = None
        self.base_count = 0
        self.references: list[_HtmlReference] = []
        self._line_offsets = [0]
        for match in re.finditer("\n", source):
            self._line_offsets.append(match.end())

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._capture_start_tag(tag, attrs)

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._capture_start_tag(tag, attrs)

    def _capture_start_tag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        raw = self.get_starttag_text() or ""
        line, column = self.getpos()
        absolute = self._line_offsets[line - 1] + column
        expected = [
            (name.lower(), value)
            for name, value in attrs
            if name.lower() in {"href", "src"}
        ]
        captured = [
            attribute
            for attribute in self._lex_start_tag(raw)
            if attribute.name in {"href", "src"}
        ]
        if [(item.name, item.value) for item in captured] != expected:
            raise BuildFailed(
                "cannot safely locate documentation href/src attributes in start tag"
            )
        if tag == "base":
            self.base_count += 1
            base_hrefs = [item for item in captured if item.name == "href"]
            if (
                self.base_count > 1
                or len(base_hrefs) > 1
                or (base_hrefs and base_hrefs[0].value not in {None, ""})
            ):
                raise BuildFailed(
                    "documentation output contains an unsafe or duplicate base element"
                )
        for attribute in captured:
            if not attribute.value:
                continue
            if attribute.start is None or attribute.end is None:
                raise BuildFailed(
                    "cannot safely locate documentation href/src attribute value"
                )
            self.references.append(
                _HtmlReference(
                    attribute.value,
                    absolute + attribute.start,
                    absolute + attribute.end,
                )
            )
            if tag == "base" and attribute.name == "href" and self.base_href is None:
                self.base_href = attribute.value

    @staticmethod
    def _lex_start_tag(raw: str) -> tuple[_StartTagAttribute, ...]:
        """Return exact attribute-value spans without scanning inside quotes."""

        if not raw.startswith("<"):
            return ()
        length = len(raw)
        cursor = 1
        while cursor < length and raw[cursor] not in _HTML_SPACE + "/>":
            cursor += 1
        result: list[_StartTagAttribute] = []
        while cursor < length:
            while cursor < length and raw[cursor] in _HTML_SPACE:
                cursor += 1
            if cursor >= length or raw[cursor] == ">":
                break
            if raw[cursor] == "/":
                cursor += 1
                continue

            name_start = cursor
            while cursor < length and raw[cursor] not in _HTML_SPACE + "/>=":
                cursor += 1
            if cursor == name_start:
                # HTMLParser accepts some malformed separators. Returning the
                # attributes seen so far makes any parsed href/src mismatch
                # fail closed in ``_capture_start_tag``.
                break
            name = raw[name_start:cursor].lower()
            while cursor < length and raw[cursor] in _HTML_SPACE:
                cursor += 1
            if cursor >= length or raw[cursor] != "=":
                result.append(_StartTagAttribute(name, None, None, None))
                continue

            while cursor < length and raw[cursor] == "=":
                cursor += 1
            while cursor < length and raw[cursor] in _HTML_SPACE:
                cursor += 1
            if cursor >= length or raw[cursor] == ">":
                result.append(_StartTagAttribute(name, "", cursor, cursor))
                continue

            quote_character = raw[cursor] if raw[cursor] in {'"', "'"} else None
            if quote_character is not None:
                cursor += 1
                value_start = cursor
                value_end = raw.find(quote_character, cursor)
                if value_end < 0:
                    break
                cursor = value_end + 1
            else:
                value_start = cursor
                while cursor < length and raw[cursor] not in _HTML_SPACE + ">":
                    cursor += 1
                value_end = cursor
            result.append(
                _StartTagAttribute(
                    name,
                    html_unescape(raw[value_start:value_end]),
                    value_start,
                    value_end,
                )
            )
        return tuple(result)


@dataclass(frozen=True)
class ProjectDocsResult:
    output_root: Path
    mode: str
    targets: tuple[str, ...]
    pages: tuple[Path, ...]
    dependency_stubs: int
    reused: bool

    def public_dict(self) -> dict[str, object]:
        return {
            "output_root": str(self.output_root),
            "mode": self.mode,
            "targets": list(self.targets),
            "pages": [str(path) for path in self.pages],
            "dependency_stubs": self.dependency_stubs,
            "reused": self.reused,
        }


@dataclass(frozen=True)
class ReachableProjectModule:
    """One project-owned Lean module selected by a documentation root."""

    name: str
    source: Path
    owners: frozenset[str]


@dataclass(frozen=True)
class ReachableProjectModulePlan:
    """Read-only, deduplicated project-module closure for documentation."""

    project_root: Path
    roots: tuple[str, ...]
    batches: tuple[tuple[ReachableProjectModule, ...], ...]

    @property
    def entries(self) -> tuple[ReachableProjectModule, ...]:
        return tuple(entry for batch in self.batches for entry in batch)

    @property
    def module_sources(self) -> tuple[tuple[str, Path], ...]:
        return tuple((entry.name, entry.source) for entry in self.entries)

    @property
    def module_owners(self) -> dict[str, frozenset[str]]:
        return {entry.name: entry.owners for entry in self.entries}


@dataclass(frozen=True)
class ProjectOleanInspection:
    """Result of resolving one reachable module to a safe compiled artifact."""

    module: str
    source: Path
    candidates: tuple[Path, ...]
    status: Literal["valid", "missing", "unsafe"]
    artifact: Path | None = None
    detail: str = ""

    @property
    def succeeded(self) -> bool:
        return self.status == "valid" and self.artifact is not None


class ProjectDocumentationBuilder:
    """Generate reachable project-module docs in an immutable cache entry.

    doc-gen4 historically rendered every transitive Mathlib page and then
    assembled one global in-memory index. That is unnecessary for ReasBook's
    per-project API pages and exceeds common CI/container memory limits. This
    adapter discovers every project-owned module reachable from the requested
    roots and analyzes them in bounded batches. Modern doc-gen4 writes a
    project-only database; legacy releases render the same bounded module set
    through a compatibility adapter. Missing external pages become explicit
    local placeholders, so both Pages and self-hosted artifacts remain
    navigable without silently publishing broken links.
    """

    def __init__(self, runner: _Runner | None = None) -> None:
        self.runner = runner or SubprocessRunner(stream=True)

    def build(
        self,
        project_root: str | Path,
        targets: tuple[str, ...] | list[str],
        output_root: str | Path,
        *,
        lake_bin: str = "lake",
        repository: str = "",
        revision: str = "",
        timeout_seconds: float = 21600.0,
    ) -> ProjectDocsResult:
        project = discover_project(project_root)
        plan = self.plan_reachable_modules(project.root, targets)
        roots = plan.roots
        batches = tuple(
            tuple((entry.name, entry.source) for entry in batch)
            for batch in plan.batches
        )
        module_sources = plan.module_sources
        module_owners = plan.module_owners
        modules = tuple(module for module, _source in module_sources)
        if not lake_bin.strip() or any(char in lake_bin for char in "\x00\r\n"):
            raise ConfigurationError("lake executable must be a safe non-empty value")
        if timeout_seconds <= 0:
            raise ConfigurationError("documentation timeout must be positive")
        repository = self._normalize_github_repository(repository)
        revision = revision.strip()
        if revision and not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ConfigurationError("documentation revision must be a full commit SHA")
        if bool(repository) != bool(revision):
            raise ConfigurationError(
                "documentation repository and revision must be provided together"
            )

        target = self._safe_output_root(output_root)
        if target in {Path("/"), project.root} or target in project.root.parents:
            raise ConfigurationError(f"unsafe documentation output root: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        # Recheck after creating missing parents so a concurrently introduced
        # link cannot redirect the cache writer before canonicalization.
        target = self._safe_output_root(target)

        docgen, mode = self._docgen(project.root, lake_bin, timeout_seconds)
        compiled_artifacts = (
            self._compiled_artifact_identity(
                project.root,
                module_sources,
                docgen,
                revision=revision,
            )
            if mode == "database"
            else None
        )
        reference_files = self._reference_files(project.root, module_sources)
        identity = {
            "schema_version": 2,
            "profile": _PROFILE,
            "module_batch_size": _MODULE_BATCH_SIZE,
            "toolchain": project.toolchain,
            "targets": list(roots),
            "modules": list(modules),
            "module_owners": [
                {"module": module, "roots": sorted(module_owners[module])}
                for module in modules
            ],
            "sources": [
                {"module": module, "sha256": self._sha256(source)}
                for module, source in module_sources
            ],
            "repository": repository,
            "revision": revision,
            "docgen_sha256": self._sha256(docgen),
            "adapter_sha256": self._sha256(self._adapter(mode)),
            "mode": mode,
            "link_policy": _LINK_POLICY,
            "statement_renderer_sha256": self._sha256(Path(statement_docs.__file__)),
            "reference_inputs": [
                {"module": module, "sha256": self._sha256(path)}
                for module, path in sorted(reference_files.items())
            ],
        }
        if compiled_artifacts is not None:
            identity["compiled_artifacts"] = compiled_artifacts
        lock = target.parent / f".{target.name}.lock"
        with self._exclusive_lock(lock):
            cached = self._cached_result(
                target,
                identity,
                roots,
                modules,
                mode,
                project_root=project.root,
                module_sources=module_sources,
                module_owners=module_owners,
                repository=repository,
                revision=revision,
            )
            if cached is not None:
                return cached
            return self._build_fresh(
                project.root,
                target,
                roots,
                batches,
                docgen,
                mode,
                identity,
                lake_bin=lake_bin,
                repository=repository,
                revision=revision,
                module_owners=module_owners,
                reference_files=reference_files,
                timeout_seconds=timeout_seconds,
            )

    @classmethod
    def _reference_files(
        cls, project_root: Path, module_sources: tuple[tuple[str, Path], ...],
    ) -> dict[str, Path]:
        """Use only metadata beside the same checked artifact used by docs.

        This shares the existing compiler/cache trust boundary; no source-name
        guessing or additional Lean compilation is performed. Metadata changes,
        including a previously absent .ilean appearing, invalidate rendered docs.
        """
        result: dict[str, Path] = {}
        for module, source in module_sources:
            if not statement_docs.source_reading(source.read_text(encoding='utf-8')).references:
                continue
            inspection = cls.inspect_project_olean(
                project_root, project_root / '.lake/build/lib/lean', module, source,
            )
            if inspection.status == 'unsafe':
                raise BuildFailed(inspection.detail)
            if not inspection.succeeded or inspection.artifact is None:
                continue
            path = inspection.artifact.with_suffix('.ilean')
            if path.is_symlink() or (path.exists() and not path.is_file()):
                raise BuildFailed(f'unsafe reference metadata: {path}')
            if path.is_file():
                result[module] = path
        return result

    def _build_fresh(
        self,
        project_root: Path,
        target: Path,
        roots: tuple[str, ...],
        batches: tuple[tuple[tuple[str, Path], ...], ...],
        docgen: Path,
        mode: str,
        identity: dict[str, object],
        *,
        lake_bin: str,
        repository: str,
        revision: str,
        module_owners: dict[str, frozenset[str]],
        reference_files: dict[str, Path],
        timeout_seconds: float,
    ) -> ProjectDocsResult:
        stage = Path(
            tempfile.mkdtemp(prefix=f".{target.name}.stage-", dir=target.parent)
        )
        backup = target.parent / f".{target.name}.backup-{uuid.uuid4().hex}"
        try:
            module_sources = tuple(item for batch in batches for item in batch)
            modules = tuple(module for module, _source in module_sources)
            analysis_identity: dict[str, object] | None = None
            checkpoint: Path | None = None
            force_analysis = False
            fallback_candidate: Path | None = None
            while True:
                restored = False
                try:
                    if mode == "database":
                        database = stage / "api-docs.db"
                        analysis_identity = self._analysis_identity(
                            project_root,
                            module_sources,
                            docgen,
                            compiled_artifacts=identity["compiled_artifacts"],
                            revision=revision,
                        )
                        checkpoint = self._analysis_checkpoint(
                            target.parent, analysis_identity
                        )
                        if not force_analysis:
                            restored = self._restore_analysis_checkpoint(
                                checkpoint, database, analysis_identity, modules
                            )
                        if not restored:
                            for sequence, batch in enumerate(batches):
                                control = stage / f".reasbook-docs-{sequence:04d}.txt"
                                try:
                                    control.write_text(
                                        "".join(
                                            f"{module}\n" for module, _source in batch
                                        ),
                                        encoding="utf-8",
                                    )
                                    self._run(
                                        project_root,
                                        (
                                            lake_bin,
                                            "-R",
                                            "-Kenv=dev",
                                            "env",
                                            "lean",
                                            "-j",
                                            "1",
                                            "-R",
                                            str(self._adapter("database").parent),
                                            *self._database_interpreter_args(
                                                project_root
                                            ),
                                            "--run",
                                            str(self._adapter("database")),
                                            str(stage),
                                            "api-docs.db",
                                            str(control),
                                        ),
                                        timeout_seconds,
                                    )
                                finally:
                                    control.unlink(missing_ok=True)
                            self._validate_analysis_database(database, modules)
                            if force_analysis:
                                fallback_candidate = (
                                    stage / ".reasbook-analysis-candidate.db"
                                )
                                self._backup_analysis_database(
                                    database, fallback_candidate
                                )
                            else:
                                self._store_analysis_checkpoint(
                                    checkpoint,
                                    database,
                                    analysis_identity,
                                    modules,
                                )
                        self._set_database_source_urls(
                            database,
                            tuple(
                                (
                                    module,
                                    self._source_uri(
                                        project_root,
                                        source,
                                        repository,
                                        revision,
                                    ),
                                )
                                for module, source in module_sources
                            ),
                        )
                        self._run(
                            project_root,
                            (
                                lake_bin,
                                "-R",
                                "-Kenv=dev",
                                "env",
                                str(docgen),
                                "fromDb",
                                "--build",
                                str(stage),
                                "--manifest",
                                str(stage / "doc-manifest.json"),
                                str(database),
                                *roots,
                            ),
                            timeout_seconds,
                        )
                    else:
                        for sequence, batch in enumerate(batches):
                            control = stage / f".reasbook-docs-{sequence:04d}.txt"
                            try:
                                control.write_text(
                                    "".join(
                                        f"{module}\t"
                                        f"{self._source_uri(project_root, source, repository, revision)}\n"
                                        for module, source in batch
                                    ),
                                    encoding="utf-8",
                                )
                                self._run(
                                    project_root,
                                    (
                                        lake_bin,
                                        "-R",
                                        "-Kenv=dev",
                                        "env",
                                        "lean",
                                        "-j",
                                        "1",
                                        "-R",
                                        str(self._adapter("legacy").parent),
                                        *self._legacy_interpreter_args(project_root),
                                        "--run",
                                        str(self._adapter("legacy")),
                                        str(stage),
                                        str(control),
                                    ),
                                    timeout_seconds,
                                )
                            finally:
                                control.unlink(missing_ok=True)
                        self._run(
                            project_root,
                            (
                                lake_bin,
                                "-R",
                                "-Kenv=dev",
                                "env",
                                str(docgen),
                                "index",
                                "--build",
                                str(stage),
                            ),
                            timeout_seconds,
                        )

                    pages = self._expected_pages(stage, modules)
                    self._validate_pages(pages)
                    if identity['reference_inputs'] != [
                        {'module': module, 'sha256': self._sha256(path)}
                        for module, path in sorted(reference_files.items())
                    ]:
                        raise BuildFailed('reference metadata changed during documentation build')
                    statement_docs.enrich_documentation(
                        stage / "doc", module_sources, module_owners,
                        {module: self._source_uri(project_root, source, repository, revision)
                         for module, source in module_sources},
                        reference_files=reference_files,
                    )
                    stub_count = self._close_documentation_links(
                        stage / "doc",
                        project_root=project_root,
                        module_sources=module_sources,
                        module_owners=module_owners,
                        repository=repository,
                        revision=revision,
                    )
                except BuildFailed:
                    if mode != "database" or not restored or force_analysis:
                        raise
                    # A structurally valid checkpoint can still be incompatible
                    # with the renderer. Retry exactly once from a completely
                    # fresh stage, retaining the published checkpoint until the
                    # fresh analysis and render have both succeeded.
                    self._remove_path(stage)
                    stage.mkdir()
                    force_analysis = True
                    fallback_candidate = None
                    continue
                break

            if fallback_candidate is not None:
                if checkpoint is None or analysis_identity is None:
                    raise BuildFailed(
                        "fresh documentation analysis lost its checkpoint identity"
                    )
                self._store_analysis_checkpoint(
                    checkpoint,
                    fallback_candidate,
                    analysis_identity,
                    modules,
                    replace_existing=True,
                )
                fallback_candidate.unlink()
            (stage / "project-docs.json").write_text(
                json.dumps(identity, ensure_ascii=True, sort_keys=True, indent=2)
                + "\n",
                encoding="utf-8",
            )
            self._validate_tree(stage)
            had_target = target.exists()
            if had_target:
                os.replace(target, backup)
            try:
                os.replace(stage, target)
            except OSError:
                if had_target and not target.exists():
                    os.replace(backup, target)
                raise
            if had_target:
                self._remove_path(backup)
            return ProjectDocsResult(
                target,
                mode,
                roots,
                self._expected_pages(target, modules),
                stub_count,
                False,
            )
        finally:
            if stage.exists():
                shutil.rmtree(stage)
            # Preserve the backup for manual recovery if both publication and
            # rollback fail.  If either operation succeeded, ``target`` exists
            # and the backup is no longer needed.
            if backup.exists() and target.exists():
                self._remove_path(backup)

    def _docgen(
        self, project_root: Path, lake_bin: str, timeout_seconds: float
    ) -> tuple[Path, str]:
        package = project_root / ".lake" / "packages" / "doc-gen4"
        executable = package / ".lake" / "build" / "bin" / "doc-gen4"
        if not executable.is_file():
            self._run(
                project_root,
                (lake_bin, "-R", "-Kenv=dev", "build", "doc-gen4"),
                timeout_seconds,
            )
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise BuildFailed(f"doc-gen4 executable is missing: {executable}")
        main = package / "Main.lean"
        try:
            source = main.read_text(encoding="utf-8")
        except OSError as exc:
            raise BuildFailed(f"cannot inspect doc-gen4 interface: {main}") from exc
        mode = "database" if re.search(r"\bfromDb\b", source) else "legacy"
        return executable.resolve(), mode

    @staticmethod
    def _normalize_github_repository(repository: str) -> str:
        """Validate and canonicalize a repository used in raw HTML attributes."""

        if repository == "":
            return ""
        if repository != repository.strip() or any(
            character.isspace() or ord(character) < 0x20 or ord(character) == 0x7F
            for character in repository
        ):
            raise ConfigurationError(
                "documentation repository must be a strict GitHub HTTPS URL"
            )
        try:
            parsed = urlsplit(repository)
            port = parsed.port
        except ValueError as exc:
            raise ConfigurationError(
                "documentation repository must be a strict GitHub HTTPS URL"
            ) from exc
        if (
            parsed.scheme != "https"
            or parsed.netloc != "github.com"
            or parsed.hostname != "github.com"
            or parsed.username is not None
            or parsed.password is not None
            or port is not None
            or parsed.query
            or parsed.fragment
        ):
            raise ConfigurationError(
                "documentation repository must be a strict GitHub HTTPS URL"
            )
        path = parsed.path.split("/")
        if len(path) != 3 or path[0] != "":
            raise ConfigurationError(
                "documentation repository must contain exactly owner and repository"
            )
        owner, name = path[1], path[2].removesuffix(".git")
        if not _GITHUB_SEGMENT_RE.fullmatch(owner) or not _GITHUB_SEGMENT_RE.fullmatch(
            name
        ):
            raise ConfigurationError(
                "documentation repository owner and name contain unsafe characters"
            )
        return f"https://github.com/{owner}/{name}"

    @staticmethod
    def _safe_output_root(output_root: str | Path) -> Path:
        """Canonicalize an output only after rejecting lexical symlinks."""

        expanded = Path(output_root).expanduser()
        lexical = Path(os.path.abspath(os.fspath(expanded)))
        current = Path(lexical.anchor)
        for part in lexical.parts[1:]:
            current /= part
            try:
                metadata = current.lstat()
            except FileNotFoundError:
                continue
            except OSError as exc:
                raise ConfigurationError(
                    f"cannot inspect documentation output path: {current}"
                ) from exc
            if stat.S_ISLNK(metadata.st_mode):
                raise ConfigurationError(
                    f"documentation output path contains a symlink: {current}"
                )
        return lexical.resolve(strict=False)

    @staticmethod
    def _adapter(mode: str) -> Path:
        name = (
            "ProjectDocsDatabase.lean"
            if mode == "database"
            else "ProjectDocsLegacy.lean"
        )
        adapter = Path(__file__).with_name("resources") / name
        if not adapter.is_file() or adapter.is_symlink():
            raise BuildFailed(f"project documentation adapter is missing: {adapter}")
        return adapter.resolve()

    @staticmethod
    def _database_interpreter_args(project_root: Path) -> tuple[str, ...]:
        """Load native modules needed by the database compatibility adapter."""

        packages = project_root / ".lake" / "packages"
        sqlite_lib = packages / "leansqlite" / ".lake" / "build" / "lib"
        required = (
            sqlite_lib / "libleansqlite.so",
            sqlite_lib / "lean" / "leansqlite_SQLite_FFI.so",
        )
        for library in required:
            if not library.is_file() or library.is_symlink():
                raise BuildFailed(
                    "doc-gen4 database adapter requires a built leansqlite "
                    f"library: {library}"
                )
        libraries = [library.resolve() for library in required]
        return tuple(f"--load-dynlib={library}" for library in libraries)

    @staticmethod
    def _legacy_interpreter_args(project_root: Path) -> tuple[str, ...]:
        """Resolve the legacy renderer's native interpreter libraries.

        Pre-database doc-gen4 renders HTML inside ``lean --run`` and therefore
        requires native implementations from both UnicodeBasic and MD4Lean.
        Both packages changed their aggregate-library names when Lake introduced
        scoped library names. Discover those explicit artifact layouts instead
        of keying behavior to a Lean version string or loading every ``.so`` in
        a package build directory.
        """

        packages = project_root / ".lake" / "packages"
        unicode_lib = packages / "UnicodeBasic" / ".lake" / "build" / "lib"
        unicode = ProjectDocumentationBuilder._unique_native_library(
            unicode_lib,
            "UnicodeBasic aggregate",
            ("libUnicodeBasic_UnicodeBasic.so", "libUnicodeBasic.so"),
        )
        md4lean_lib = packages / "MD4Lean" / ".lake" / "build" / "lib"
        main = ProjectDocumentationBuilder._unique_native_library(
            md4lean_lib,
            "MD4Lean aggregate",
            ("libMD4Lean_MD4Lean.so", "libMD4Lean.so"),
        )
        # Providers precede consumers. UnicodeBasic's aggregate contains both
        # the Lean wrapper and its Unicode C lookup implementation; MD4Lean's C
        # bridge similarly precedes the MD4Lean aggregate that calls it.
        md4c = ProjectDocumentationBuilder._safe_native_library(
            md4lean_lib / "libleanmd4c.so", "MD4Lean C"
        )
        libraries = [unicode, md4c, main]
        return tuple(f"--load-dynlib={library}" for library in libraries)

    @staticmethod
    def _unique_native_library(
        directory: Path,
        label: str,
        filenames: tuple[str, ...],
    ) -> Path:
        """Select one known aggregate layout and reject stale/unsafe artifacts."""

        candidates = tuple(directory / filename for filename in filenames)
        present = tuple(
            library
            for library in candidates
            if library.exists() or library.is_symlink()
        )
        if len(present) != 1:
            supported = ", ".join(filenames)
            raise BuildFailed(
                "project documentation adapter requires exactly one supported "
                f"{label} library under {directory} ({supported})"
            )
        return ProjectDocumentationBuilder._safe_native_library(present[0], label)

    @staticmethod
    def _safe_native_library(library: Path, label: str) -> Path:
        try:
            safe = (
                library.is_file()
                and not library.is_symlink()
                and library.stat().st_size > 0
            )
        except OSError as exc:
            raise BuildFailed(f"cannot inspect {label} library: {library}") from exc
        if not safe:
            raise BuildFailed(f"{label} library is unsafe: {library}")
        return library.resolve()

    def _run(self, cwd: Path, argv: tuple[str, ...], timeout_seconds: float) -> None:
        result = self.runner.run(
            Command(
                argv=argv,
                cwd=cwd,
                env={"DISABLE_EQUATIONS": "1", "LEAN_NUM_THREADS": "1"},
                timeout=timeout_seconds,
            )
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise BuildFailed(
                "documentation command failed"
                + (f": {detail[-1000:]}" if detail else "")
            )

    @staticmethod
    def _normalize_targets(values: tuple[str, ...] | list[str]) -> tuple[str, ...]:
        modules: list[str] = []
        for value in values:
            module = str(value).strip().split(":", 1)[0]
            if not _MODULE_RE.fullmatch(module):
                raise ConfigurationError(f"invalid documentation module: {value!r}")
            if module not in modules:
                modules.append(module)
        if not modules:
            raise ConfigurationError("at least one documentation module is required")
        return tuple(modules)

    @classmethod
    def plan_reachable_modules(
        cls,
        project_root: str | Path,
        targets: tuple[str, ...] | list[str],
    ) -> ReachableProjectModulePlan:
        """Plan the project-owned import closure without invoking Lean or Lake.

        Candidate discovery spans the project root, so cross-book imports do
        not depend on selecting the imported book's root. Only modules reached
        from a selected root enter the result. Modules reached by more than one
        entry root occur once and retain the complete transitive owner set.
        Unresolved imports are external unless a supported project-local path
        is hidden behind an unsafe existing filesystem component.
        Batches preserve the bounded analyzer ordering used by :meth:`build`.
        """

        project = discover_project(project_root)
        roots = cls._normalize_targets(targets)
        batches, owners = cls._module_plan(project.root, roots)
        return ReachableProjectModulePlan(
            project_root=project.root,
            roots=roots,
            batches=tuple(
                tuple(
                    ReachableProjectModule(module, source, owners[module])
                    for module, source in batch
                )
                for batch in batches
            ),
        )

    @classmethod
    def project_olean_candidates(
        cls,
        project_root: str | Path,
        compiled_root: str | Path,
        module: str,
        source: str | Path,
    ) -> tuple[Path, ...]:
        """Return supported Lake `.olean` layouts in deterministic priority order."""

        if not _MODULE_RE.fullmatch(module):
            raise ConfigurationError(f"invalid documentation module: {module!r}")
        root_path = Path(project_root).expanduser()
        try:
            root = root_path.resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise BuildFailed(f"cannot inspect project root: {root_path}") from exc
        if not root.is_dir():
            raise BuildFailed(f"project root is not a directory: {root}")
        source_path = Path(source)
        try:
            source_metadata = source_path.lstat()
            resolved_source = source_path.resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise BuildFailed(f"cannot inspect project module: {source_path}") from exc
        if stat.S_ISLNK(source_metadata.st_mode) or not stat.S_ISREG(
            source_metadata.st_mode
        ):
            raise BuildFailed(f"project module source is unsafe: {source_path}")
        try:
            relative_source = resolved_source.relative_to(root).with_suffix(".olean")
        except ValueError as exc:
            raise BuildFailed(
                f"project module source escapes its root: {source_path}"
            ) from exc

        compiled = Path(compiled_root).expanduser()
        module_path = Path(*module.split(".")).with_suffix(".olean")
        relative_candidates = [module_path, relative_source]
        if relative_source.parts[0] in {"Books", "Papers"}:
            relative_candidates.append(Path(*relative_source.parts[1:]))

        candidates: list[Path] = []
        seen: set[Path] = set()
        for relative in relative_candidates:
            candidate = compiled / relative
            if candidate not in seen:
                seen.add(candidate)
                candidates.append(candidate)
        return tuple(candidates)

    @classmethod
    def inspect_project_olean(
        cls,
        project_root: str | Path,
        compiled_root: str | Path,
        module: str,
        source: str | Path,
    ) -> ProjectOleanInspection:
        """Resolve one module to a non-empty regular `.olean` without following links.

        A symlink or non-directory in a candidate's existing parent chain is
        unsafe, as is a symlink, non-regular, or empty candidate. Once a
        higher-priority candidate exists but is unsafe, lower-priority layouts
        are not considered.
        """

        lexical_root = Path(compiled_root).expanduser()
        if not lexical_root.is_absolute():
            lexical_root = Path.cwd() / lexical_root
        candidates = cls.project_olean_candidates(
            project_root, lexical_root, module, source
        )
        reported_candidates = candidates

        def result(
            status: Literal["valid", "missing", "unsafe"],
            detail: str,
            *,
            artifact: Path | None = None,
        ) -> ProjectOleanInspection:
            return ProjectOleanInspection(
                module=module,
                source=Path(source),
                candidates=reported_candidates,
                status=status,
                artifact=artifact,
                detail=detail,
            )

        try:
            root_metadata = lexical_root.lstat()
        except FileNotFoundError:
            return result(
                "missing",
                detail=f"compiled artifact directory is missing: {lexical_root}",
            )
        except OSError as exc:
            return result(
                "unsafe",
                detail=f"cannot inspect compiled artifact directory: {exc}",
            )
        if stat.S_ISLNK(root_metadata.st_mode) or not stat.S_ISDIR(
            root_metadata.st_mode
        ):
            return result(
                "unsafe",
                detail=f"compiled artifact directory is unsafe: {lexical_root}",
            )
        try:
            resolved_root = lexical_root.resolve(strict=True)
        except OSError as exc:
            return result(
                "unsafe",
                detail=f"cannot resolve compiled artifact directory: {exc}",
            )

        reported_candidates = tuple(
            resolved_root / candidate.relative_to(lexical_root)
            for candidate in candidates
        )
        for candidate in reported_candidates:
            relative = candidate.relative_to(resolved_root)
            current = resolved_root
            missing_parent = False
            for part in relative.parts[:-1]:
                current = current / part
                try:
                    metadata = current.lstat()
                except FileNotFoundError:
                    missing_parent = True
                    break
                except OSError as exc:
                    return result(
                        "unsafe",
                        detail=f"cannot inspect compiled artifact path {current}: {exc}",
                    )
                if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
                    return result(
                        "unsafe",
                        detail=f"compiled artifact path is unsafe: {current}",
                    )
            if missing_parent:
                continue
            try:
                metadata = candidate.lstat()
            except FileNotFoundError:
                continue
            except OSError as exc:
                return result(
                    "unsafe",
                    detail=f"cannot inspect compiled artifact {candidate}: {exc}",
                )
            if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
                return result(
                    "unsafe",
                    detail=f"compiled artifact is unsafe: {candidate}",
                )
            if metadata.st_size <= 0:
                return result(
                    "unsafe",
                    detail=f"compiled artifact is empty: {candidate}",
                )
            return result(
                "valid",
                detail="",
                artifact=candidate,
            )
        return result(
            "missing",
            detail=f"compiled olean is missing for documentation module {module}",
        )

    @classmethod
    def _module_batches(
        cls,
        project_root: Path,
        roots: tuple[str, ...],
    ) -> tuple[tuple[tuple[str, Path], ...], ...]:
        batches, _owners = cls._module_plan(project_root, roots)
        return batches

    @classmethod
    def _module_plan(
        cls,
        project_root: Path,
        roots: tuple[str, ...],
    ) -> tuple[
        tuple[tuple[tuple[str, Path], ...], ...],
        dict[str, frozenset[str]],
    ]:
        """Split each project closure into bounded analyzer batches."""

        batches: list[tuple[tuple[str, Path], ...]] = []
        seen: dict[str, Path] = {}
        owners: dict[str, set[str]] = {}
        candidates = cls._project_module_candidates(project_root, roots)
        imports: dict[Path, tuple[str, ...]] = {}
        checked_external_imports: set[str] = set()
        for root in roots:
            fresh: list[tuple[str, Path]] = []
            for module, source in cls._reachable_project_module_sources(
                project_root,
                root,
                candidates,
                imports,
                checked_external_imports,
            ):
                owners.setdefault(module, set()).add(root)
                previous = seen.get(module)
                if previous is not None:
                    if previous != source:
                        raise BuildFailed(
                            f"project module {module} resolves to multiple source files"
                        )
                    continue
                seen[module] = source
                fresh.append((module, source))
            for offset in range(0, len(fresh), _MODULE_BATCH_SIZE):
                batches.append(tuple(fresh[offset : offset + _MODULE_BATCH_SIZE]))
        if not batches:
            raise BuildFailed("no project-owned documentation modules were discovered")
        return tuple(batches), {
            module: frozenset(values) for module, values in owners.items()
        }

    @staticmethod
    def _module_lexical_sources(project_root: Path, module: str) -> tuple[Path, ...]:
        parts = module.split(".")
        relative = Path(*parts).with_suffix(".lean")
        candidates = [project_root / relative]
        if parts[0] not in {"Books", "Papers"}:
            candidates.extend(
                (project_root / kind / relative for kind in ("Books", "Papers"))
            )
        lakefile = project_root / "lakefile.lean"
        if lakefile.is_file():
            for source_dir in parse_library_declarations(lakefile).values():
                if source_dir:
                    candidates.append(project_root / source_dir / relative)
        return tuple(dict.fromkeys(candidates))

    @classmethod
    def _module_source(cls, project_root: Path, module: str) -> Path:
        candidates = cls._module_lexical_sources(project_root, module)
        matches = [path for path in candidates if path.is_file()]
        parts = module.split(".")
        if not matches and len(parts) == 1:
            matches = sorted(project_root.glob(f"Books/**/{parts[0]}.lean"))
            matches += sorted(project_root.glob(f"Papers/**/{parts[0]}.lean"))
        if len(matches) != 1:
            raise BuildFailed(
                f"cannot uniquely resolve source file for documentation module {module}"
            )
        return matches[0]

    @classmethod
    def _project_module_candidates(
        cls,
        project_root: Path,
        roots: tuple[str, ...],
    ) -> dict[str, tuple[Path, ...]]:
        """Index project-owned sources once without selecting every orphan.

        Repository-relative names support aggregate modules. Stripping a
        leading ``Books`` or ``Papers`` supports Lake libraries whose
        ``srcDir`` points at that directory, including explicit roots. The
        index may contain ambiguous or unsafe orphan sources; those are
        rejected only if a selected root reaches them.
        """

        candidates: dict[str, set[Path]] = {}
        lakefile = project_root / "lakefile.lean"
        source_dirs = tuple(
            Path(value).parts
            for value in dict.fromkeys(parse_library_declarations(lakefile).values())
            if value
        ) if lakefile.is_file() else ()

        def register(module: str, source: Path) -> None:
            if _MODULE_RE.fullmatch(module):
                candidates.setdefault(module, set()).add(source)

        def walk_error(error: OSError) -> None:
            raise BuildFailed(
                f"cannot discover project documentation sources: {error}"
            ) from error

        for raw_directory, directories, files in os.walk(
            project_root,
            topdown=True,
            followlinks=False,
            onerror=walk_error,
        ):
            directories[:] = sorted(
                name for name in directories if name not in {".git", ".lake"}
            )
            directory = Path(raw_directory)
            for filename in sorted(files):
                if not filename.endswith(".lean"):
                    continue
                source = directory / filename
                relative = source.relative_to(project_root).with_suffix("")
                register(".".join(relative.parts), source)
                if relative.parts[0] in {"Books", "Papers"} and len(relative.parts) > 1:
                    register(".".join(relative.parts[1:]), source)
                for source_dir in source_dirs:
                    if relative.parts[:len(source_dir)] == source_dir:
                        register(".".join(relative.parts[len(source_dir):]), source)

        # Preserve the historical single-component fallback and fail early for
        # an invalid selected root. The global index supplies cross-project
        # imports even when their own Book/Paper root is not selected.
        for root in roots:
            source = cls._module_source(project_root, root)
            register(root, source)

        return {
            module: tuple(sorted(sources, key=str))
            for module, sources in candidates.items()
        }

    @classmethod
    def _reachable_project_module_sources(
        cls,
        project_root: Path,
        root: str,
        candidates: dict[str, tuple[Path, ...]],
        imports: dict[Path, tuple[str, ...]],
        checked_external_imports: set[str],
    ) -> tuple[tuple[str, Path], ...]:
        """Traverse one root on the shared project-source candidate graph."""

        reachable: dict[str, Path] = {}
        pending = [root]
        while pending:
            module = pending.pop()
            if module in reachable:
                continue
            sources = candidates.get(module)
            if sources is None:
                if module == root:
                    raise BuildFailed(
                        f"project root {module} is outside its discovered source layout"
                    )
                continue
            source = cls._safe_project_module_source(
                project_root,
                module,
                sources,
            )
            reachable[module] = source
            imported_modules = imports.get(source)
            if imported_modules is None:
                imported_modules = cls._source_imports(source)
                imports[source] = imported_modules
            for imported in reversed(imported_modules):
                if imported in candidates:
                    if imported not in reachable:
                        pending.append(imported)
                    continue
                if imported not in checked_external_imports:
                    cls._reject_unsafe_unresolved_project_import(
                        project_root,
                        imported,
                    )
                    checked_external_imports.add(imported)

        return tuple(sorted(reachable.items()))

    @classmethod
    def _reject_unsafe_unresolved_project_import(
        cls,
        project_root: Path,
        module: str,
    ) -> None:
        """Fail when an unresolved import is hidden behind an unsafe local path.

        A missing lexical component means the import can be external. Existing
        components must remain real directories up to a regular ``.lean``
        leaf; otherwise candidate discovery could silently skip a project-owned
        source (notably beneath an untraversed directory symlink).
        """

        for candidate in cls._module_lexical_sources(project_root, module):
            cls._resolve_safe_project_source(
                project_root,
                candidate,
                subject=f"unresolved project import {module}",
                allow_missing=True,
            )

    @staticmethod
    def _resolve_safe_project_source(
        project_root: Path,
        source: Path,
        *,
        subject: str,
        allow_missing: bool,
    ) -> Path | None:
        """Resolve a source only after a lexical no-follow chain inspection."""

        try:
            relative = source.relative_to(project_root)
        except ValueError as exc:
            raise BuildFailed(f"{subject} escapes its project root: {source}") from exc
        current = project_root
        for index, part in enumerate(relative.parts):
            current = current / part
            try:
                metadata = current.lstat()
            except FileNotFoundError:
                if allow_missing:
                    return None
                raise BuildFailed(f"cannot inspect {subject}: {current}") from None
            except OSError as exc:
                raise BuildFailed(f"cannot inspect {subject}: {current}") from exc
            is_leaf = index == len(relative.parts) - 1
            expected_type = stat.S_ISREG if is_leaf else stat.S_ISDIR
            if stat.S_ISLNK(metadata.st_mode) or not expected_type(metadata.st_mode):
                raise BuildFailed(f"{subject} crosses an unsafe source path: {current}")
        try:
            resolved = source.resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            raise BuildFailed(f"cannot resolve {subject}: {source}") from exc
        if project_root not in resolved.parents:
            raise BuildFailed(f"{subject} escapes its project root: {source}")
        return resolved

    @classmethod
    def _safe_project_module_source(
        cls,
        project_root: Path,
        module: str,
        sources: tuple[Path, ...],
    ) -> Path:
        if len(sources) != 1:
            raise BuildFailed(
                f"project module {module} resolves to multiple source files"
            )
        source = sources[0]
        resolved = cls._resolve_safe_project_source(
            project_root,
            source,
            subject=f"project module {module}",
            allow_missing=False,
        )
        assert resolved is not None
        if resolved.suffix != ".lean":
            raise BuildFailed(f"project module source is not Lean: {source}")
        return resolved

    @staticmethod
    def _source_imports(source: Path) -> tuple[str, ...]:
        try:
            lines = source.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError as exc:
            raise BuildFailed(f"cannot read project module: {source}") from exc
        imports: list[str] = []
        for line in lines:
            match = _IMPORT_RE.match(line.split("--", 1)[0])
            if not match:
                continue
            for token in match.group(1).split():
                module = token.strip("`«»")
                if _MODULE_RE.fullmatch(module) and module not in imports:
                    imports.append(module)
        return tuple(imports)

    @staticmethod
    def _set_database_source_urls(
        database: Path,
        module_urls: tuple[tuple[str, str], ...],
    ) -> None:
        if database.is_symlink():
            raise BuildFailed(
                f"documentation database must not be a symlink: {database}"
            )
        expected = {module for module, _url in module_urls}
        try:
            with closing(sqlite3.connect(database)) as connection:
                with connection:
                    rows = connection.execute("SELECT name FROM modules").fetchall()
                    actual = {str(row[0]) for row in rows}
                    if actual != expected:
                        missing = sorted(expected - actual)
                        unexpected = sorted(actual - expected)
                        raise BuildFailed(
                            "documentation database module mismatch"
                            f"; missing={missing[:10]}; unexpected={unexpected[:10]}"
                        )
                    connection.executemany(
                        "UPDATE modules SET source_url = ? WHERE name = ?",
                        ((url, module) for module, url in module_urls),
                    )
        except sqlite3.Error as exc:
            raise BuildFailed(f"cannot update documentation database: {exc}") from exc

    @classmethod
    def _analysis_identity(
        cls,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        docgen: Path,
        *,
        compiled_artifacts: object,
        revision: str,
    ) -> dict[str, object]:
        """Describe the expensive doc-gen analysis independently of rendering."""

        manifest = project_root / "lake-manifest.json"
        return {
            "schema_version": 1,
            "profile": _ANALYSIS_PROFILE,
            "module_batch_size": _MODULE_BATCH_SIZE,
            "toolchain": (project_root / "lean-toolchain")
            .read_text(encoding="utf-8")
            .strip(),
            "revision": revision,
            "lake_manifest_sha256": cls._sha256(manifest)
            if manifest.is_file() and not manifest.is_symlink()
            else None,
            "modules": [module for module, _source in module_sources],
            "sources": [
                {"module": module, "sha256": cls._sha256(source)}
                for module, source in module_sources
            ],
            "docgen_sha256": cls._sha256(docgen),
            "adapter_sha256": cls._sha256(cls._adapter("database")),
            "compiled_artifacts": compiled_artifacts,
        }

    @classmethod
    def _compiled_artifact_identity(
        cls,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        docgen: Path,
        *,
        revision: str,
    ) -> dict[str, object]:
        """Digest analyzer inputs not represented by Lean source hashes.

        Managed branch caches bind dependency builds through their immutable
        cache metadata. Reachable project oleans and analyzer-native support
        files are always content-hashed. An unmanaged local Lake tree has no
        such trust boundary, so all package oleans/native archives are hashed.
        """

        lake = project_root / ".lake"
        project_build = lake / "build"
        project_lib = project_build / "lib" / "lean"
        packages = lake / "packages"
        artifacts: dict[Path, str] = {}

        def register(path: Path, logical: str) -> None:
            try:
                unsafe = (
                    path.is_symlink() or not path.is_file() or path.stat().st_size == 0
                )
            except OSError as exc:
                raise BuildFailed(f"cannot inspect compiled artifact: {path}") from exc
            if unsafe:
                raise BuildFailed(f"compiled artifact is missing or unsafe: {path}")
            resolved = path.resolve()
            previous = artifacts.get(resolved)
            artifacts[resolved] = (
                logical if previous is None else min(previous, logical)
            )

        for module, source in module_sources:
            module_path = Path(*module.split(".")).with_suffix(".olean")
            inspection = cls.inspect_project_olean(
                project_root, project_lib, module, source
            )
            if not inspection.succeeded:
                raise BuildFailed(inspection.detail)
            artifact = inspection.artifact
            if artifact is None:
                raise BuildFailed(inspection.detail)
            register(artifact, f"project/{module_path.as_posix()}")

        metadata_path = lake / "cache-metadata.json"
        branch_cache: dict[str, object] | None = None
        dependency_artifacts_are_immutable = False
        # An arbitrary metadata file inside a normal Lake workspace is not a
        # trust signal. Only an explicit symlink to a validated branch or
        # project-finalizer namespace can select a managed-cache policy;
        # malformed opt-ins fail closed.
        if lake.is_symlink() and (metadata_path.exists() or metadata_path.is_symlink()):
            managed_cache = cls._managed_lake_cache_identity(
                project_root,
                lake,
                revision=revision,
            )
            branch_cache = managed_cache.value
            dependency_artifacts_are_immutable = (
                managed_cache.dependency_artifacts_are_immutable
            )

        dependency_packages: tuple[Path, ...]
        if not dependency_artifacts_are_immutable:
            try:
                dependency_packages = tuple(
                    sorted(path for path in packages.iterdir() if path.is_dir())
                )
            except OSError as exc:
                raise BuildFailed(f"cannot inspect Lake packages: {packages}") from exc
        else:
            dependency_packages = tuple(
                packages / name for name in ("doc-gen4", "leansqlite")
            )

        scan_roots = [(project_build, "project-build")]
        scan_roots.extend(
            (package / ".lake" / "build", f"packages/{package.name}")
            for package in dependency_packages
        )
        for root, prefix in scan_roots:
            if not root.is_dir():
                continue
            for path in sorted(root.rglob("*")):
                if path.suffix not in _COMPILED_ARTIFACT_SUFFIXES:
                    continue
                if prefix == "project-build" and path.suffix == ".olean":
                    continue
                register(path, f"{prefix}/{path.relative_to(root).as_posix()}")

        register(docgen, "packages/doc-gen4/bin/doc-gen4")
        for argument in cls._database_interpreter_args(project_root):
            library = Path(argument.removeprefix("--load-dynlib="))
            register(library, f"native/{library.name}")

        digest = hashlib.sha256()
        total_bytes = 0
        for path, logical in sorted(
            artifacts.items(), key=lambda item: (item[1], str(item[0]))
        ):
            before = path.stat()
            content_sha256 = cls._sha256(path)
            after = path.stat()
            if (
                before.st_dev,
                before.st_ino,
                before.st_size,
                before.st_mtime_ns,
                before.st_ctime_ns,
            ) != (
                after.st_dev,
                after.st_ino,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            ):
                raise BuildFailed(f"compiled artifact changed while hashing: {path}")
            encoded = f"{logical}\0{before.st_size}\0{content_sha256}\n".encode()
            digest.update(encoded)
            total_bytes += before.st_size
        if not artifacts:
            raise BuildFailed("no compiled artifacts were found for documentation")
        return {
            "schema_version": 1,
            "policy": "reachable-project-content-and-dependency-cache-v1",
            "branch_cache": branch_cache,
            "file_count": len(artifacts),
            "total_bytes": total_bytes,
            "sha256": digest.hexdigest(),
        }

    @classmethod
    def _managed_branch_cache_identity(
        cls,
        project_root: Path,
        lake: Path,
        *,
        revision: str,
    ) -> dict[str, object]:
        """Validate the structural opt-in for an immutable branch cache."""

        return cls._managed_lake_cache_identity(
            project_root,
            lake,
            revision=revision,
        ).value

    @staticmethod
    def _read_managed_cache_json(path: Path, *, label: str) -> object:
        """Read one small regular metadata file without following a leaf link."""

        flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(path, flags)
        except OSError as exc:
            raise BuildFailed(f"cannot open {label}: {path}") from exc
        try:
            metadata = os.fstat(descriptor)
            if (
                not stat.S_ISREG(metadata.st_mode)
                or metadata.st_size <= 0
                or metadata.st_size > _MAX_MANAGED_CACHE_METADATA_BYTES
            ):
                raise BuildFailed(f"{label} has an unsafe size or file type")
            with os.fdopen(descriptor, "r", encoding="utf-8", closefd=False) as handle:
                try:
                    return json.load(handle)
                except (UnicodeError, json.JSONDecodeError) as exc:
                    raise BuildFailed(f"{label} is invalid") from exc
        finally:
            os.close(descriptor)

    @classmethod
    def _managed_lake_cache_identity(
        cls,
        project_root: Path,
        lake: Path,
        *,
        revision: str,
    ) -> _ManagedCacheIdentity:
        """Validate an immutable branch cache or isolated writable project cache.

        A direct ``lake/<branch-namespace>`` cache outside the
        ``finalizer-caches`` namespace is immutable and may bind dependency
        artifacts through its structural identity. Project finalizers use
        ``lake/<branch-namespace>/projects/<project-component>``. Those
        workspaces are deliberately writable, so their exact schema-3 marker
        is part of the checkpoint identity and every dependency artifact is
        still content-hashed.
        """

        try:
            cache = lake.resolve(strict=True)
        except OSError as exc:
            raise BuildFailed(f"managed Lake cache link is invalid: {lake}") from exc
        metadata_path = cache / "cache-metadata.json"
        manifest = project_root / "lake-manifest.json"
        toolchain_file = project_root / "lean-toolchain"
        if (
            not lake.is_symlink()
            or not cache.is_dir()
            or cache.is_symlink()
            or metadata_path.is_symlink()
            or not metadata_path.is_file()
            or manifest.is_symlink()
            or not manifest.is_file()
            or toolchain_file.is_symlink()
            or not toolchain_file.is_file()
        ):
            raise BuildFailed("managed Lake cache has an unsafe namespace layout")
        metadata = cls._read_managed_cache_json(
            metadata_path,
            label="compiled branch cache metadata",
        )
        try:
            toolchain = toolchain_file.read_text(encoding="utf-8").strip()
        except OSError as exc:
            raise BuildFailed("compiled branch cache metadata is invalid") from exc
        if (
            not isinstance(metadata, dict)
            or set(metadata) != _MANAGED_CACHE_METADATA_KEYS
        ):
            raise BuildFailed("compiled branch cache metadata has an unknown purpose")

        branch = metadata.get("branch")
        commit = metadata.get("commit")
        manifest_sha256 = cls._sha256(manifest)
        expected_toolchain = cls._cache_component(toolchain.rsplit(":", 1)[-1])
        architecture = cls._cache_component(platform.machine() or "unknown")
        if (
            not isinstance(branch, str)
            or branch != branch.strip()
            or branch in {".", ".."}
            or branch.startswith("/")
            or ".." in branch
            or not _BRANCH_RE.fullmatch(branch)
            or not isinstance(commit, str)
            or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or (revision and commit != revision)
            or metadata.get("schema") != 1
            or metadata.get("manifest_sha256") != manifest_sha256
            or metadata.get("toolchain") != expected_toolchain
            or metadata.get("architecture") != architecture
        ):
            raise BuildFailed(
                "compiled branch cache metadata does not match this project or host"
            )
        expected_name = (
            f"branch-{cls._cache_component(branch)}-{commit[:12]}-"
            f"{manifest_sha256[:16]}-{expected_toolchain}-{architecture}"
        )
        direct_branch_cache = cache.parent.name == "lake"
        project_cache = cache.parent.name == "projects"
        branch_namespace = cache if direct_branch_cache else cache.parent.parent
        if (
            not (direct_branch_cache or project_cache)
            or branch_namespace.name != expected_name
        ):
            raise BuildFailed(
                "managed Lake cache namespace does not match its branch metadata"
            )
        if direct_branch_cache:
            if cache.parent.is_symlink() or not cache.parent.is_dir():
                raise BuildFailed("managed Lake cache has an unsafe namespace layout")
            finalizer_positions = tuple(
                index
                for index, parent in enumerate(cache.parents)
                if parent.name == "finalizer-caches"
            )
            finalizer_marker = cache / "finalizer-cache.json"
            if (
                finalizer_positions
                or finalizer_marker.exists()
                or finalizer_marker.is_symlink()
            ):
                if len(finalizer_positions) != 1 or finalizer_positions[0] not in {
                    2,
                    3,
                }:
                    raise BuildFailed(
                        "managed Lake cache has an unsafe namespace layout"
                    )
                return cls._managed_finalizer_cache_identity(
                    cache,
                    metadata_path=metadata_path,
                    branch_namespace=branch_namespace,
                    branch=branch,
                    commit=commit,
                    manifest_sha256=manifest_sha256,
                    toolchain=expected_toolchain,
                    architecture=architecture,
                    project_cache=False,
                )
            return _ManagedCacheIdentity(
                {
                    "policy": "trusted-immutable-branch-cache-v1",
                    "purpose": "release-branch-build",
                    "namespace": expected_name,
                    "metadata_sha256": cls._sha256(metadata_path),
                    "branch": branch,
                    "commit": commit,
                    "manifest_sha256": manifest_sha256,
                    "toolchain": expected_toolchain,
                    "architecture": architecture,
                },
                dependency_artifacts_are_immutable=True,
            )

        return cls._managed_finalizer_cache_identity(
            cache,
            metadata_path=metadata_path,
            branch_namespace=branch_namespace,
            branch=branch,
            commit=commit,
            manifest_sha256=manifest_sha256,
            toolchain=expected_toolchain,
            architecture=architecture,
            project_cache=True,
        )

    @classmethod
    def _managed_finalizer_cache_identity(
        cls,
        cache: Path,
        *,
        metadata_path: Path,
        branch_namespace: Path,
        branch: str,
        commit: str,
        manifest_sha256: str,
        toolchain: str,
        architecture: str,
        project_cache: bool,
    ) -> _ManagedCacheIdentity:
        """Validate one exact writable branch/project finalizer cache."""

        if project_cache:
            projects = cache.parent
            lake_namespace = branch_namespace.parent
            configuration_namespace: Path | None = lake_namespace.parent
            tooling_namespace = configuration_namespace.parent
            finalizer_namespace = tooling_namespace.parent
            layout = (
                (cache, None),
                (projects, "projects"),
                (branch_namespace, None),
                (lake_namespace, "lake"),
                (configuration_namespace, None),
                (tooling_namespace, None),
                (finalizer_namespace, "finalizer-caches"),
            )
        else:
            lake_namespace = cache.parent
            legacy_finalizer = lake_namespace.parent.parent
            configured_finalizer = legacy_finalizer.parent
            if legacy_finalizer.name == "finalizer-caches":
                configuration_namespace = None
                tooling_namespace = lake_namespace.parent
                finalizer_namespace = legacy_finalizer
            elif configured_finalizer.name == "finalizer-caches":
                configuration_namespace = lake_namespace.parent
                tooling_namespace = configuration_namespace.parent
                finalizer_namespace = configured_finalizer
            else:
                raise BuildFailed("managed Lake cache has an unsafe namespace layout")
            layout = (
                (cache, None),
                (lake_namespace, "lake"),
                (tooling_namespace, None),
                (finalizer_namespace, "finalizer-caches"),
            )
            if configuration_namespace is not None:
                layout += ((configuration_namespace, None),)
        if any(
            path.is_symlink()
            or not path.is_dir()
            or (expected is not None and path.name != expected)
            for path, expected in layout
        ):
            raise BuildFailed("managed Lake cache has an unsafe namespace layout")

        tooling_digest = tooling_namespace.name
        configuration_name = (
            configuration_namespace.name
            if configuration_namespace is not None
            else None
        )
        configuration_digest = (
            configuration_name.removeprefix("cfg-")
            if configuration_name is not None
            else None
        )
        marker_path = cache / "finalizer-cache.json"
        if (
            not _SHA256_RE.fullmatch(tooling_digest)
            or (
                configuration_name is not None
                and (
                    not configuration_name.startswith("cfg-")
                    or configuration_digest is None
                    or not _SHA256_RE.fullmatch(configuration_digest)
                )
            )
            or marker_path.is_symlink()
            or not marker_path.is_file()
        ):
            raise BuildFailed("managed Lake cache has an unsafe namespace layout")
        marker = cls._read_managed_cache_json(
            marker_path,
            label="finalizer cache metadata",
        )
        expected_keys = (
            _PROJECT_FINALIZER_METADATA_KEYS
            if project_cache
            else _CONFIGURED_FINALIZER_METADATA_KEYS
            if configuration_namespace is not None
            else _FINALIZER_METADATA_KEYS
        )
        expected_schema = 3 if configuration_namespace is not None else 2
        if (
            not isinstance(marker, dict)
            or set(marker) != expected_keys
            or marker.get("schema") != expected_schema
            or marker.get("purpose") != "release-finalizer-lean-workspace"
            or marker.get("workspace_policy") != "persistent-writable-v1"
        ):
            raise BuildFailed("finalizer cache metadata has an unknown purpose")

        project_key = marker.get("project_key")
        configuration = marker.get("build_configuration")
        if project_cache and (
            not isinstance(project_key, str)
            or cls._cache_component(project_key) != cache.name
        ):
            raise BuildFailed("finalizer cache metadata does not match its path")
        actual_configuration_digest: str | None = None
        if configuration_namespace is not None:
            if (
                not isinstance(configuration, dict)
                or set(configuration) != _FINALIZER_BUILD_CONFIGURATION_KEYS
                or configuration.get("schema") != 1
                or isinstance(configuration.get("lean_threads"), bool)
                or not isinstance(configuration.get("lean_threads"), int)
                or not 1 <= configuration["lean_threads"] <= 256
                or isinstance(configuration.get("lake_threads"), bool)
                or configuration.get("lake_threads") != 1
            ):
                raise BuildFailed(
                    "finalizer cache metadata has an invalid configuration"
                )
            actual_configuration_digest = hashlib.sha256(
                json.dumps(
                    configuration,
                    ensure_ascii=True,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
        if (
            marker.get("branch") != branch
            or marker.get("commit") != commit
            or marker.get("manifest_sha256") != manifest_sha256
            or marker.get("toolchain") != toolchain
            or marker.get("architecture") != architecture
            or marker.get("tooling_sha256") != tooling_digest
            or marker.get("seed_namespace") != branch_namespace.name
            or (
                configuration_namespace is not None
                and (
                    marker.get("build_configuration_sha256")
                    != actual_configuration_digest
                    or configuration_digest != actual_configuration_digest
                )
            )
        ):
            raise BuildFailed("finalizer cache metadata identity mismatch")
        identity: dict[str, object] = {
            "policy": (
                "validated-writable-project-finalizer-cache-v1"
                if project_cache
                else "validated-writable-branch-finalizer-cache-v1"
            ),
            "purpose": "release-finalizer-lean-workspace",
            "namespace": branch_namespace.name,
            "metadata_sha256": cls._sha256(metadata_path),
            "finalizer_metadata_sha256": cls._sha256(marker_path),
            "branch": branch,
            "commit": commit,
            "manifest_sha256": manifest_sha256,
            "toolchain": toolchain,
            "architecture": architecture,
            "tooling_sha256": tooling_digest,
        }
        if actual_configuration_digest is not None:
            identity["build_configuration_sha256"] = actual_configuration_digest
        if project_cache:
            identity.update(
                {
                    "project_namespace": cache.name,
                    "project_key": project_key,
                }
            )
        return _ManagedCacheIdentity(
            identity,
            dependency_artifacts_are_immutable=False,
        )

    @staticmethod
    def _cache_component(value: str) -> str:
        """Match the branch-cache producer's bounded filesystem component."""

        normalized = re.sub(r"[^A-Za-z0-9._-]+", "_", value.strip()).strip("._")
        if not normalized:
            raise BuildFailed("managed Lake cache identity has an empty component")
        return normalized[:160]

    @staticmethod
    def _analysis_checkpoint(parent: Path, identity: dict[str, object]) -> Path:
        serialized = json.dumps(
            identity, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
        digest = hashlib.sha256(serialized).hexdigest()
        return parent / f".{_ANALYSIS_PROFILE}" / digest

    @classmethod
    def _restore_analysis_checkpoint(
        cls,
        checkpoint: Path,
        destination: Path,
        identity: dict[str, object],
        modules: tuple[str, ...],
    ) -> bool:
        cls._ensure_analysis_cache_root(checkpoint.parent)
        lock = checkpoint.parent / f".{checkpoint.name}.lock"
        if lock.is_symlink():
            raise BuildFailed(f"documentation analysis lock is unsafe: {lock}")
        with cls._exclusive_lock(lock):
            if not cls._valid_analysis_checkpoint(checkpoint, identity, modules):
                return False
            shutil.copy2(checkpoint / "api-docs.db", destination)
        cls._validate_analysis_database(destination, modules, immutable=True)
        return True

    @classmethod
    def _store_analysis_checkpoint(
        cls,
        checkpoint: Path,
        database: Path,
        identity: dict[str, object],
        modules: tuple[str, ...],
        *,
        replace_existing: bool = False,
    ) -> None:
        root = checkpoint.parent
        cls._ensure_analysis_cache_root(root)
        lock = root / f".{checkpoint.name}.lock"
        if lock.is_symlink():
            raise BuildFailed(f"documentation analysis lock is unsafe: {lock}")
        with cls._exclusive_lock(lock):
            if not replace_existing and cls._valid_analysis_checkpoint(
                checkpoint, identity, modules
            ):
                return
            stage = Path(
                tempfile.mkdtemp(prefix=f".{checkpoint.name}.stage-", dir=root)
            )
            backup = root / f".{checkpoint.name}.backup-{uuid.uuid4().hex}"
            try:
                staged_database = stage / "api-docs.db"
                cls._backup_analysis_database(database, staged_database)
                database_schema = cls._validate_analysis_database(
                    staged_database, modules, immutable=True
                )
                marker = {
                    "schema_version": 1,
                    "identity": identity,
                    "database_bytes": staged_database.stat().st_size,
                    "database_sha256": cls._sha256(staged_database),
                    "database_schema": database_schema,
                }
                (stage / "analysis.json").write_text(
                    json.dumps(marker, ensure_ascii=True, sort_keys=True, indent=2)
                    + "\n",
                    encoding="utf-8",
                )
                had_checkpoint = checkpoint.exists() or checkpoint.is_symlink()
                if had_checkpoint:
                    os.replace(checkpoint, backup)
                try:
                    os.replace(stage, checkpoint)
                except OSError:
                    if had_checkpoint and not checkpoint.exists():
                        os.replace(backup, checkpoint)
                    raise
                if had_checkpoint:
                    cls._remove_path(backup)
            finally:
                if stage.exists():
                    cls._remove_path(stage)
                if backup.exists() and checkpoint.exists():
                    cls._remove_path(backup)

    @classmethod
    def _valid_analysis_checkpoint(
        cls,
        checkpoint: Path,
        identity: dict[str, object],
        modules: tuple[str, ...],
    ) -> bool:
        marker = checkpoint / "analysis.json"
        database = checkpoint / "api-docs.db"
        try:
            if checkpoint.is_symlink() or not checkpoint.is_dir():
                return False
            if marker.is_symlink() or database.is_symlink():
                return False
            if {path.name for path in checkpoint.iterdir()} != {
                "analysis.json",
                "api-docs.db",
            }:
                return False
            payload = json.loads(marker.read_text(encoding="utf-8"))
            if not isinstance(payload, dict):
                return False
            if (
                payload.get("schema_version") != 1
                or payload.get("identity") != identity
                or payload.get("database_bytes") != database.stat().st_size
                or payload.get("database_sha256") != cls._sha256(database)
            ):
                return False
            expected_schema = payload.get("database_schema")
            if not isinstance(expected_schema, dict):
                return False
            if (
                cls._validate_analysis_database(database, modules, immutable=True)
                != expected_schema
            ):
                return False
        except (BuildFailed, OSError, ValueError, json.JSONDecodeError):
            return False
        return True

    @staticmethod
    def _ensure_analysis_cache_root(root: Path) -> None:
        if root.exists() and (not root.is_dir() or root.is_symlink()):
            raise BuildFailed(f"documentation analysis cache is unsafe: {root}")
        root.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _validate_analysis_database(
        database: Path,
        modules: tuple[str, ...],
        *,
        immutable: bool = False,
    ) -> dict[str, object]:
        if (
            database.is_symlink()
            or not database.is_file()
            or database.stat().st_size == 0
        ):
            raise BuildFailed(f"documentation analysis database is unsafe: {database}")
        try:
            suffix = "?mode=ro" + ("&immutable=1" if immutable else "")
            with closing(
                sqlite3.connect(database.resolve().as_uri() + suffix, uri=True)
            ) as connection:
                check = connection.execute("PRAGMA quick_check").fetchone()
                if check != ("ok",):
                    raise BuildFailed(
                        f"documentation analysis database is corrupt: {database}"
                    )
                rows = connection.execute(
                    "SELECT name, source_url FROM modules"
                ).fetchall()
                schema_binding = ProjectDocumentationBuilder._database_schema_binding(
                    connection
                )
        except sqlite3.Error as exc:
            raise BuildFailed(
                f"cannot validate documentation analysis database: {exc}"
            ) from exc
        actual = {str(row[0]) for row in rows}
        if actual != set(modules) or len(rows) != len(modules):
            raise BuildFailed("documentation analysis database module mismatch")
        if any(row[1] not in {None, ""} for row in rows):
            raise BuildFailed(
                "documentation analysis checkpoint contains rendered source URLs"
            )
        return schema_binding

    @staticmethod
    def _database_schema_binding(connection: sqlite3.Connection) -> dict[str, object]:
        """Bind a checkpoint to doc-gen's real SQLite schema contract."""

        try:
            schema_rows = connection.execute(
                "SELECT type, name, tbl_name, sql FROM sqlite_schema "
                "WHERE name NOT LIKE 'sqlite_%' ORDER BY type, name, tbl_name"
            ).fetchall()
            table_names = {str(row[1]) for row in schema_rows if str(row[0]) == "table"}
            missing = sorted(_ANALYZER_REQUIRED_TABLES - table_names)
            if missing:
                raise BuildFailed(
                    "documentation analysis database schema is incomplete: "
                    + ", ".join(missing)
                )
            meta_rows = connection.execute(
                "SELECT key, value FROM schema_meta ORDER BY key"
            ).fetchall()
        except sqlite3.Error as exc:
            raise BuildFailed(
                f"cannot inspect documentation analysis schema: {exc}"
            ) from exc
        schema_meta = {str(key): str(value) for key, value in meta_rows}
        if (
            len(schema_meta) != len(meta_rows)
            or not _ANALYZER_SCHEMA_META_KEYS.issubset(schema_meta)
            or any(not schema_meta[key] for key in _ANALYZER_SCHEMA_META_KEYS)
        ):
            raise BuildFailed(
                "documentation analysis database has invalid schema metadata"
            )
        serialized = json.dumps(
            [
                [str(value) if value is not None else None for value in row]
                for row in schema_rows
            ],
            ensure_ascii=True,
            separators=(",", ":"),
        ).encode()
        return {
            "schema_version": 1,
            "sqlite_schema_sha256": hashlib.sha256(serialized).hexdigest(),
            "schema_meta": schema_meta,
            "required_tables": sorted(_ANALYZER_REQUIRED_TABLES),
        }

    @staticmethod
    def _backup_analysis_database(source: Path, destination: Path) -> None:
        """Create a standalone SQLite snapshot, folding in any WAL content."""

        if source.is_symlink() or not source.is_file() or destination.exists():
            raise BuildFailed(f"documentation analysis database is unsafe: {source}")
        try:
            with closing(
                sqlite3.connect(source.resolve().as_uri() + "?mode=ro", uri=True)
            ) as source_connection:
                with closing(sqlite3.connect(destination)) as destination_connection:
                    with destination_connection:
                        source_connection.backup(destination_connection)
                        journal_mode = destination_connection.execute(
                            "PRAGMA journal_mode=DELETE"
                        ).fetchone()
                        if journal_mode != ("delete",):
                            raise BuildFailed(
                                "cannot make documentation analysis snapshot standalone"
                            )
        except sqlite3.Error as exc:
            raise BuildFailed(
                f"cannot snapshot documentation analysis database: {exc}"
            ) from exc

    @staticmethod
    def _source_uri(
        project_root: Path, source: Path, repository: str, revision: str
    ) -> str:
        if not repository:
            return "#"
        relative = source.relative_to(project_root).as_posix()
        return f"{repository}/blob/{revision}/ReasBook/{quote(relative, safe='/')}"

    @staticmethod
    def _expected_pages(root: Path, modules: tuple[str, ...]) -> tuple[Path, ...]:
        return tuple(
            root / "doc" / Path(*module.split(".")).with_suffix(".html")
            for module in modules
        )

    @staticmethod
    def _validate_pages(pages: tuple[Path, ...]) -> None:
        missing = []
        for page in pages:
            try:
                content = page.read_text(encoding="utf-8", errors="replace")
            except OSError:
                content = ""
            if (
                page.is_symlink()
                or len(content.strip()) < 64
                or "<html" not in content.lower()
            ):
                missing.append(str(page))
        if missing:
            raise BuildFailed(
                "documentation output is missing or invalid: " + ", ".join(missing)
            )

    @classmethod
    def _cached_result(
        cls,
        target: Path,
        identity: dict[str, object],
        roots: tuple[str, ...],
        modules: tuple[str, ...],
        mode: str,
        *,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        module_owners: dict[str, frozenset[str]],
        repository: str,
        revision: str,
    ) -> ProjectDocsResult | None:
        marker = target / "project-docs.json"
        try:
            cached_identity = json.loads(marker.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
        pages = cls._expected_pages(target, modules)
        try:
            cls._validate_pages(pages)
            cls._validate_tree(target)
        except BuildFailed:
            return None
        if cached_identity == identity:
            try:
                cls._close_documentation_links(
                    target / "doc",
                    project_root=project_root,
                    module_sources=module_sources,
                    module_owners=module_owners,
                    repository=repository,
                    revision=revision,
                    allow_writes=False,
                )
            except BuildFailed:
                return None
        else:
            legacy_identity = dict(identity)
            legacy_identity.pop("link_policy", None)
            if cached_identity != legacy_identity:
                return None
            if not cls._migrate_cached_links(
                target,
                identity,
                modules,
                project_root=project_root,
                module_sources=module_sources,
                module_owners=module_owners,
                repository=repository,
                revision=revision,
            ):
                return None
            pages = cls._expected_pages(target, modules)
        stubs = sum(
            1 for path in (target / "doc").rglob("*.html") if cls._is_stub(path)
        )
        return ProjectDocsResult(target, mode, roots, pages, stubs, True)

    @classmethod
    def _migrate_cached_links(
        cls,
        target: Path,
        identity: dict[str, object],
        modules: tuple[str, ...],
        *,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        module_owners: dict[str, frozenset[str]],
        repository: str,
        revision: str,
    ) -> bool:
        """Upgrade a pre-link-policy cache through an isolated atomic copy."""

        stage = Path(
            tempfile.mkdtemp(prefix=f".{target.name}.migration-", dir=target.parent)
        )
        stage.rmdir()
        backup = target.parent / f".{target.name}.backup-{uuid.uuid4().hex}"
        try:
            shutil.copytree(target, stage, symlinks=True)
            cls._close_documentation_links(
                stage / "doc",
                project_root=project_root,
                module_sources=module_sources,
                module_owners=module_owners,
                repository=repository,
                revision=revision,
            )
            (stage / "project-docs.json").write_text(
                json.dumps(identity, ensure_ascii=True, sort_keys=True, indent=2)
                + "\n",
                encoding="utf-8",
            )
            cls._validate_pages(cls._expected_pages(stage, modules))
            cls._validate_tree(stage)
            os.replace(target, backup)
            try:
                os.replace(stage, target)
            except OSError:
                if not target.exists():
                    os.replace(backup, target)
                raise
            cls._remove_path(backup)
        except (BuildFailed, OSError, shutil.Error):
            return False
        finally:
            if stage.exists():
                cls._remove_path(stage)
            if backup.exists() and target.exists():
                cls._remove_path(backup)
        return True

    @classmethod
    def _close_documentation_links(
        cls,
        doc_root: Path,
        *,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        module_owners: dict[str, frozenset[str]],
        repository: str,
        revision: str,
        allow_writes: bool = True,
    ) -> int:
        """Close internal links and pin recognized project source links.

        A local ``.lean`` reference is rewritten only when its path has a
        unique suffix match in the reachable source set.  If multiple books
        contain the same suffix, the source module of the referring page may
        disambiguate it only through the exact selected-root ownership graph.
        Everything else remains a missing non-HTML asset and fails closed.
        """

        if not (doc_root / "index.html").is_file():
            raise BuildFailed("documentation output has no index.html")
        stylesheet = doc_root / "style.css"
        if (
            stylesheet.is_symlink()
            or not stylesheet.is_file()
            or stylesheet.stat().st_size == 0
        ):
            raise BuildFailed("documentation output has no safe style.css")
        missing_assets: list[str] = []
        stubs: set[Path] = set()
        for document in sorted(doc_root.rglob("*.html")):
            content = document.read_text(encoding="utf-8", errors="replace")
            parser = _LinkParser(content)
            parser.feed(content)
            document_url = (
                "https://docs.invalid/" + document.relative_to(doc_root).as_posix()
            )
            base_url = urljoin(document_url, parser.base_href or "")
            edits: list[tuple[int, int, str]] = []
            for item in parser.references:
                reference = item.value.strip()
                if not reference or reference.startswith("#"):
                    continue
                try:
                    raw_url = urlsplit(reference)
                except ValueError as exc:
                    raise BuildFailed(
                        f"documentation link has an invalid URL: {reference!r}"
                    ) from exc
                scheme = raw_url.scheme.lower()
                if scheme:
                    if scheme in {"http", "https"} and raw_url.netloc:
                        continue
                    if scheme in {"data", "mailto"}:
                        continue
                    raise BuildFailed(
                        f"documentation link uses an unsafe scheme: {reference!r}"
                    )
                if raw_url.netloc:
                    raise BuildFailed(
                        "documentation link uses a protocol-relative URL: "
                        f"{reference!r}"
                    )
                decoded_reference = unquote(reference)
                if (
                    "\\" in decoded_reference
                    or "\x00" in decoded_reference
                    or _WINDOWS_ABSOLUTE_RE.match(decoded_reference)
                ):
                    raise BuildFailed(
                        f"documentation link has an unsafe path: {reference!r}"
                    )
                resolved = urlsplit(urljoin(base_url, reference))
                if resolved.scheme != "https" or resolved.netloc != "docs.invalid":
                    raise BuildFailed(
                        f"documentation link escapes its synthetic origin: {reference!r}"
                    )
                relative_text = unquote(resolved.path).lstrip("/")
                if not relative_text:
                    continue
                if "\\" in relative_text or "\x00" in relative_text:
                    raise BuildFailed(
                        f"documentation link has an unsafe path: {reference!r}"
                    )
                relative = Path(relative_text)
                if any(part in {"", ".", ".."} for part in relative.parts):
                    raise BuildFailed(
                        f"documentation link has an unsafe path: {reference}"
                    )
                target = (doc_root / relative).resolve(strict=False)
                if doc_root not in target.parents:
                    raise BuildFailed(
                        f"documentation link escapes its root: {reference}"
                    )
                if resolved.path.endswith("/") or target.is_dir():
                    target /= "index.html"
                if target.is_file():
                    continue
                immutable = cls._immutable_project_source_link(
                    document,
                    doc_root,
                    resolved.path,
                    resolved.query,
                    resolved.fragment,
                    project_root=project_root,
                    module_sources=module_sources,
                    module_owners=module_owners,
                    repository=repository,
                    revision=revision,
                )
                if immutable is not None:
                    if allow_writes:
                        edits.append((item.start, item.end, immutable))
                        continue
                    missing_assets.append(
                        f"{document.relative_to(doc_root)} -> {reference} "
                        "(source link is not normalized)"
                    )
                elif target.suffix.lower() in {".html", ".htm"}:
                    if allow_writes:
                        cls._write_stub(doc_root, target)
                        stubs.add(target)
                    else:
                        missing_assets.append(
                            f"{document.relative_to(doc_root)} -> {reference}"
                        )
                else:
                    missing_assets.append(
                        f"{document.relative_to(doc_root)} -> {reference}"
                    )
            if edits:
                for start, end, replacement in sorted(edits, reverse=True):
                    content = content[:start] + replacement + content[end:]
                document.write_text(content, encoding="utf-8")
        if missing_assets:
            raise BuildFailed(
                "documentation output references missing assets: "
                + "; ".join(missing_assets[:20])
            )
        if allow_writes:
            cls._close_documentation_links(
                doc_root,
                project_root=project_root,
                module_sources=module_sources,
                module_owners=module_owners,
                repository=repository,
                revision=revision,
                allow_writes=False,
            )
        return len(stubs)

    @classmethod
    def _immutable_project_source_link(
        cls,
        document: Path,
        doc_root: Path,
        resolved_path: str,
        query: str,
        fragment: str,
        *,
        project_root: Path,
        module_sources: tuple[tuple[str, Path], ...],
        module_owners: dict[str, frozenset[str]],
        repository: str,
        revision: str,
    ) -> str | None:
        if not repository or not revision or query:
            return None
        decoded = unquote(resolved_path)
        parts = tuple(part for part in decoded.split("/") if part not in {"", "."})
        if (
            len(parts) < 2
            or any(part == ".." for part in parts)
            or not parts[-1].lower().endswith(".lean")
        ):
            return None
        document_module = ".".join(document.relative_to(doc_root).with_suffix("").parts)
        referring_source = dict(module_sources).get(document_module)
        if referring_source is None:
            return None
        try:
            referring_text = referring_source.read_text(
                encoding="utf-8", errors="replace"
            )
        except OSError:
            return None
        # The rendered path must come from the current immutable source, not
        # merely resemble one of its filenames. This also exposes stale olean
        # caches whose docstrings no longer match the checked-out source.
        if decoded not in referring_text:
            return None

        scored: list[tuple[int, str, Path]] = []
        for module, source in module_sources:
            current = source.relative_to(project_root).parts
            score = 0
            for old_part, current_part in zip(reversed(parts), reversed(current)):
                if old_part != current_part:
                    break
                score += 1
            if score >= 2:
                scored.append((score, module, source))
        if not scored:
            return None
        best_score = max(score for score, _module, _source in scored)
        candidates = [item for item in scored if item[0] == best_score]
        if len(candidates) != 1:
            document_owners = module_owners.get(document_module, frozenset())
            candidates = [
                item
                for item in candidates
                if document_owners.intersection(module_owners.get(item[1], frozenset()))
            ]
        if len(candidates) != 1:
            return None
        result = cls._source_uri(project_root, candidates[0][2], repository, revision)
        if fragment:
            result += "#" + quote(unquote(fragment), safe="-._~:")
        return result

    @staticmethod
    def _write_stub(doc_root: Path, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        depth = len(path.relative_to(doc_root).parts) - 1
        prefix = "../" * depth
        path.write_text(
            "\n".join(
                (
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                    "  <title>Dependency documentation</title>",
                    f'  <link rel="stylesheet" href="{prefix}style.css" />',
                    "</head>",
                    '<body data-reasbook-doc-stub="true">',
                    "  <main>",
                    "    <h1>Dependency documentation</h1>",
                    "    <p>This external API page is outside the bounded project module "
                    "set. The project documentation, source, and theorem map remain "
                    "available.</p>",
                    f'    <p><a href="{prefix}index.html">Documentation index</a></p>',
                    "  </main>",
                    "</body>",
                    "</html>",
                    "",
                )
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _is_stub(path: Path) -> bool:
        try:
            return 'data-reasbook-doc-stub="true"' in path.read_text(
                encoding="utf-8", errors="ignore"
            )
        except OSError:
            return False

    @staticmethod
    def _validate_tree(root: Path) -> None:
        if not root.is_dir() or root.is_symlink():
            raise BuildFailed(f"documentation cache is not a directory: {root}")
        for path in root.rglob("*"):
            if path.is_symlink() or (not path.is_file() and not path.is_dir()):
                raise BuildFailed(
                    f"documentation cache contains an unsafe file: {path}"
                )

    @staticmethod
    def _sha256(path: Path) -> str:
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        return digest.hexdigest()

    @staticmethod
    def _remove_path(path: Path) -> None:
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink(missing_ok=True)

    @staticmethod
    @contextmanager
    def _exclusive_lock(path: Path) -> Iterator[None]:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a+b") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def plan_reachable_project_modules(
    project_root: str | Path,
    targets: tuple[str, ...] | list[str],
) -> ReachableProjectModulePlan:
    """Return the read-only, project-owned closure for documentation roots."""

    return ProjectDocumentationBuilder.plan_reachable_modules(project_root, targets)


def project_olean_candidates(
    project_root: str | Path,
    compiled_root: str | Path,
    module: str,
    source: str | Path,
) -> tuple[Path, ...]:
    """Return the supported project `.olean` paths in priority order."""

    return ProjectDocumentationBuilder.project_olean_candidates(
        project_root, compiled_root, module, source
    )


def inspect_project_olean(
    project_root: str | Path,
    compiled_root: str | Path,
    module: str,
    source: str | Path,
) -> ProjectOleanInspection:
    """Inspect one reachable project `.olean` using no-follow semantics."""

    return ProjectDocumentationBuilder.inspect_project_olean(
        project_root, compiled_root, module, source
    )


__all__ = [
    "ProjectDocumentationBuilder",
    "ProjectDocsResult",
    "ProjectOleanInspection",
    "ReachableProjectModule",
    "ReachableProjectModulePlan",
    "inspect_project_olean",
    "plan_reachable_project_modules",
    "project_olean_candidates",
]
