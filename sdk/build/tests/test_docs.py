from __future__ import annotations

from contextlib import closing
import hashlib
import json
import platform
import re
import sqlite3
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from reasbook_build_sdk import (
    BuildFailed,
    CommandResult,
    ConfigurationError,
    ProjectDocumentationBuilder,
    inspect_project_olean,
    plan_reachable_project_modules,
    project_olean_candidates,
)
from reasbook_build_sdk import docs as docs_module


class _TrackingConnection(sqlite3.Connection):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.was_closed = False

    def close(self) -> None:
        self.was_closed = True
        super().close()


class _DocsRunner:
    def __init__(self) -> None:
        self.modules: list[str] = []
        self.commands = []

    def run(self, command):
        self.commands.append(command)
        argv = command.argv
        if "--run" in argv:
            adapter = Path(argv[argv.index("--run") + 1])
            control = Path(argv[-1])
            if adapter.name == "ProjectDocsDatabase.lean":
                build = Path(argv[-3])
                modules = tuple(control.read_text(encoding="utf-8").splitlines())
                database = build / argv[-2]
                with closing(sqlite3.connect(database)) as connection:
                    with connection:
                        connection.execute("PRAGMA journal_mode=WAL")
                        connection.execute(
                            "CREATE TABLE IF NOT EXISTS modules "
                            "(name TEXT PRIMARY KEY, source_url TEXT)"
                        )
                        connection.execute(
                            "CREATE TABLE IF NOT EXISTS schema_meta "
                            "(key TEXT PRIMARY KEY, value TEXT NOT NULL)"
                        )
                        connection.executemany(
                            "INSERT OR REPLACE INTO schema_meta (key, value) VALUES (?, ?)",
                            (
                                ("ddl_hash", "fixture-ddl"),
                                ("type_hash", "fixture-types"),
                            ),
                        )
                        for table in sorted(
                            docs_module._ANALYZER_REQUIRED_TABLES
                            - {"modules", "schema_meta"}
                        ):
                            connection.execute(
                                f'CREATE TABLE IF NOT EXISTS "{table}" (fixture INTEGER)'
                            )
                        connection.executemany(
                            "INSERT INTO modules (name, source_url) VALUES (?, NULL)",
                            ((module,) for module in modules),
                        )
            else:
                build = Path(argv[-2])
                modules = tuple(
                    line.split("\t", 1)[0]
                    for line in control.read_text(encoding="utf-8").splitlines()
                )
            self.modules.extend(modules)
        elif "fromDb" in argv or "index" in argv:
            build = Path(argv[argv.index("--build") + 1])
            if "fromDb" in argv and not self.modules:
                database = Path(argv[argv.index("--manifest") + 2])
                with closing(sqlite3.connect(database)) as connection:
                    self.modules.extend(
                        str(row[0])
                        for row in connection.execute(
                            "SELECT name FROM modules ORDER BY name"
                        ).fetchall()
                    )
            doc = build / "doc"
            doc.mkdir(parents=True, exist_ok=True)
            (doc / "style.css").write_text("body{}", encoding="utf-8")
            (doc / "index.html").write_text(
                "<!doctype html><html><body>documentation index</body></html>\n",
                encoding="utf-8",
            )
            for module in self.modules:
                page = doc / Path(*module.split(".")).with_suffix(".html")
                page.parent.mkdir(parents=True, exist_ok=True)
                page.write_text(
                    "<!doctype html><html><body><h1>Project API</h1>"
                    '<a href="../../Mathlib/Dependency.html">dependency</a>'
                    "<p>This page is deliberately long enough to pass validation.</p>"
                    "</body></html>\n",
                    encoding="utf-8",
                )
        return CommandResult(command=command, returncode=0)


class _BrokenRenderRunner(_DocsRunner):
    def run(self, command):
        result = super().run(command)
        if "fromDb" in command.argv:
            build = Path(command.argv[command.argv.index("--build") + 1])
            (build / "doc" / "index.html").write_text(
                '<html><body><img src="missing.png"></body></html>',
                encoding="utf-8",
            )
        return result


class _CommandRenderFailureRunner(_DocsRunner):
    def __init__(self, *, always: bool) -> None:
        super().__init__()
        self.always = always
        self.render_attempts = 0

    def run(self, command):
        result = super().run(command)
        if "fromDb" in command.argv:
            self.render_attempts += 1
            if self.always or self.render_attempts == 1:
                return CommandResult(
                    command=command,
                    returncode=1,
                    stderr="simulated incompatible checkpoint",
                )
        return result


class ProjectDocumentationTests(unittest.TestCase):
    @staticmethod
    def _package_lib(project: Path, package: str) -> Path:
        return project / ".lake" / "packages" / package / ".lake" / "build" / "lib"

    @staticmethod
    def _write_olean(
        project: Path, module: str, content: bytes = b"olean fixture"
    ) -> Path:
        artifact = (
            project / ".lake" / "build" / "lib" / "lean" / Path(*module.split("."))
        ).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(content)
        return artifact

    def _project(self, root: Path, *, modern: bool) -> Path:
        project = root / "ReasBook"
        project.mkdir()
        (project / "lakefile.lean").write_text(
            "package ReasBook where\n", encoding="utf-8"
        )
        (project / "lean-toolchain").write_text(
            "leanprover/lean4:v4.30.0\n", encoding="utf-8"
        )
        module = project / "Books" / "Demo" / "Book.lean"
        module.parent.mkdir(parents=True)
        module.write_text(
            "import Mathlib\nimport Books.Demo.Chapter\n",
            encoding="utf-8",
        )
        (module.parent / "Chapter.lean").write_text(
            "import Mathlib\n",
            encoding="utf-8",
        )
        (module.parent / "Dead.lean").write_text(
            "import Mathlib\n",
            encoding="utf-8",
        )
        for compiled_module in (
            "Books.Demo.Book",
            "Books.Demo.Chapter",
            "Demo.Book",
            "Demo.Chapter",
        ):
            self._write_olean(project, compiled_module)
        package = project / ".lake" / "packages" / "doc-gen4"
        executable = package / ".lake" / "build" / "bin" / "doc-gen4"
        executable.parent.mkdir(parents=True)
        executable.write_text("fixture", encoding="utf-8")
        executable.chmod(0o755)
        (package / "Main.lean").write_text(
            "def fromDb := ()\n" if modern else "def index := ()\n",
            encoding="utf-8",
        )
        md4lean = self._package_lib(project, "MD4Lean") / (
            "libMD4Lean_MD4Lean.so" if modern else "libMD4Lean.so"
        )
        md4lean.parent.mkdir(parents=True)
        md4lean.write_bytes(b"fixture")
        (md4lean.parent / "libleanmd4c.so").write_bytes(b"fixture")
        unicode = self._package_lib(project, "UnicodeBasic") / (
            "libUnicodeBasic_UnicodeBasic.so" if modern else "libUnicodeBasic.so"
        )
        unicode.parent.mkdir(parents=True)
        unicode.write_bytes(b"fixture")
        if modern:
            sqlite_ffi = (
                project
                / ".lake"
                / "packages"
                / "leansqlite"
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "leansqlite_SQLite_FFI.so"
            )
            sqlite_ffi.parent.mkdir(parents=True)
            sqlite_ffi.write_bytes(b"fixture")
            (sqlite_ffi.parent.parent / "libleansqlite.so").write_bytes(b"fixture")
        return project

    @staticmethod
    def _managed_finalizer_cache(
        root: Path,
        project: Path,
        *,
        project_key: str | None = "books/Demo",
        configured: bool = True,
    ) -> tuple[Path, dict[str, object], dict[str, object], str, str]:
        if project_key is not None and not configured:
            raise ValueError("project finalizer fixtures require a configuration")
        manifest = project / "lake-manifest.json"
        manifest.write_text('{"version": 1}\n', encoding="utf-8")
        manifest_digest = ProjectDocumentationBuilder._sha256(manifest)
        branch = "v4.30.0"
        commit = "a" * 40
        toolchain = "v4.30.0"
        architecture = platform.machine() or "unknown"
        namespace = (
            f"branch-{branch}-{commit[:12]}-{manifest_digest[:16]}-"
            f"{toolchain}-{architecture}"
        )
        configuration: dict[str, object] = {
            "schema": 1,
            "lean_threads": 8,
            "lake_threads": 1,
        }
        configuration_digest = hashlib.sha256(
            json.dumps(
                configuration,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        tooling_digest = "b" * 64
        finalizer_root = root / "managed" / "finalizer-caches" / tooling_digest
        if configured:
            finalizer_root /= f"cfg-{configuration_digest}"
        branch_cache = finalizer_root / "lake" / namespace
        cache = branch_cache
        if project_key is not None:
            component = ProjectDocumentationBuilder._cache_component(project_key)
            cache = branch_cache / "projects" / component
        cache.parent.mkdir(parents=True)
        (project / ".lake").rename(cache)
        (project / ".lake").symlink_to(cache, target_is_directory=True)
        branch_metadata: dict[str, object] = {
            "schema": 1,
            "branch": branch,
            "commit": commit,
            "manifest_sha256": manifest_digest,
            "toolchain": toolchain,
            "architecture": architecture,
        }
        (cache / "cache-metadata.json").write_text(
            json.dumps(branch_metadata), encoding="utf-8"
        )
        finalizer_metadata: dict[str, object] = {
            "schema": 3 if configured else 2,
            "purpose": "release-finalizer-lean-workspace",
            "workspace_policy": "persistent-writable-v1",
            "branch": branch,
            "commit": commit,
            "manifest_sha256": manifest_digest,
            "toolchain": toolchain,
            "architecture": architecture,
            "tooling_sha256": tooling_digest,
            "seed_namespace": namespace,
        }
        if configured:
            finalizer_metadata.update(
                {
                    "build_configuration": configuration,
                    "build_configuration_sha256": configuration_digest,
                }
            )
        if project_key is not None:
            finalizer_metadata["project_key"] = project_key
        (cache / "finalizer-cache.json").write_text(
            json.dumps(finalizer_metadata), encoding="utf-8"
        )
        return (
            cache,
            branch_metadata,
            finalizer_metadata,
            namespace,
            configuration_digest,
        )

    @staticmethod
    def _cross_project_sources(
        project: Path,
        *,
        b_imports_helper: bool,
    ) -> None:
        a_root = project / "Books" / "A"
        b_root = project / "Books" / "B"
        a_root.mkdir()
        b_root.mkdir()
        (a_root / "Book.lean").write_text(
            "import B.Helper\n",
            encoding="utf-8",
        )
        (b_root / "Book.lean").write_text(
            "import B.Helper\n" if b_imports_helper else "import Mathlib\n",
            encoding="utf-8",
        )
        (b_root / "Helper.lean").write_text("import Mathlib\n", encoding="utf-8")
        (b_root / "Orphan.lean").write_text("import Mathlib\n", encoding="utf-8")
        paper_root = project / "Papers" / "B"
        paper_root.mkdir(parents=True)
        (paper_root / "Orphan.lean").write_text("import Mathlib\n", encoding="utf-8")

    def test_reachable_plan_supports_aggregate_layout_and_excludes_orphans(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)

            plan = plan_reachable_project_modules(project, ("Books.Demo.Book",))

            self.assertEqual(plan.roots, ("Books.Demo.Book",))
            self.assertEqual(
                tuple(entry.name for entry in plan.entries),
                ("Books.Demo.Book", "Books.Demo.Chapter"),
            )
            self.assertNotIn("Books.Demo.Dead", plan.module_owners)
            self.assertEqual(
                plan.module_owners["Books.Demo.Chapter"],
                frozenset({"Books.Demo.Book"}),
            )

    def test_reachable_plan_supports_flat_layout(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            (project / "Books/Demo/Book.lean").write_text(
                "import Demo.Chapter\n", encoding="utf-8"
            )

            plan = plan_reachable_project_modules(project, ("Demo.Book",))

            self.assertEqual(
                tuple(entry.name for entry in plan.entries),
                ("Demo.Book", "Demo.Chapter"),
            )

    def test_reachable_plan_supports_explicit_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            papers = project / "Papers"
            papers.mkdir()
            (papers / "Theory.lean").write_text(
                "import Theory.Current\n", encoding="utf-8"
            )
            namespace = papers / "Theory"
            namespace.mkdir()
            (namespace / "Current.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            (namespace / "Unused.lean").write_text("import Mathlib\n", encoding="utf-8")

            plan = plan_reachable_project_modules(project, ("Theory",))

            self.assertEqual(
                tuple(entry.name for entry in plan.entries),
                ("Theory", "Theory.Current"),
            )

    def test_reachable_plan_follows_nested_library_roots(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            (project / "lakefile.lean").write_text(
                'import Lake\nopen Lake DSL\nlean_lib Demo where\n'
                '  srcDir := "Papers"\n  roots := #[`Demo.Paper]\n'
                'lean_lib Core where\n  srcDir := "Papers/Demo"\n'
                '  roots := #[`Theory]\n', encoding="utf-8")
            paper = project / "Papers/Demo"
            (paper / "Theory").mkdir(parents=True)
            (paper / "Paper.lean").write_text("import Theory.Result\n")
            (paper / "Theory/Result.lean").write_text("import Mathlib\n")
            (paper / "Theory/Unused.lean").write_text("import Mathlib\n")
            plan = plan_reachable_project_modules(project, ("Demo.Paper",))
            self.assertEqual(tuple(entry.name for entry in plan.entries),
                             ("Demo.Paper", "Theory.Result"))

    def test_reachable_plan_deduplicates_shared_modules_and_records_owners(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)

            plan = plan_reachable_project_modules(
                project,
                ("Books.Demo.Book", "Books.Demo.Chapter"),
            )

            names = tuple(entry.name for entry in plan.entries)
            self.assertEqual(names.count("Books.Demo.Chapter"), 1)
            self.assertEqual(
                plan.module_owners["Books.Demo.Chapter"],
                frozenset({"Books.Demo.Book", "Books.Demo.Chapter"}),
            )

    def test_reachable_plan_follows_cross_project_import_without_second_root(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            self._cross_project_sources(project, b_imports_helper=False)

            plan = plan_reachable_project_modules(project, ("A.Book",))

            self.assertEqual(
                tuple(entry.name for entry in plan.entries),
                ("A.Book", "B.Helper"),
            )
            self.assertEqual(
                plan.module_owners["B.Helper"],
                frozenset({"A.Book"}),
            )
            self.assertNotIn("B.Book", plan.module_owners)
            self.assertNotIn("B.Orphan", plan.module_owners)

    def test_reachable_plan_rejects_import_hidden_by_symlink_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            a_root = project / "Books" / "A"
            a_root.mkdir()
            (a_root / "Book.lean").write_text(
                "import B.Helper\n",
                encoding="utf-8",
            )
            real_b = project / "RealB"
            real_b.mkdir()
            (real_b / "Helper.lean").write_text("import Mathlib\n", encoding="utf-8")
            (project / "Books" / "B").symlink_to(Path("../RealB"))

            with self.assertRaisesRegex(
                BuildFailed,
                r"unresolved project import B[.]Helper crosses an unsafe source path",
            ):
                plan_reachable_project_modules(project, ("A.Book",))

    def test_reachable_plan_rejects_selected_root_under_symlink_directory(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            real_b = project / "RealB"
            real_b.mkdir()
            (real_b / "Book.lean").write_text("import Mathlib\n", encoding="utf-8")
            (project / "Books" / "B").symlink_to(Path("../RealB"))

            with self.assertRaisesRegex(
                BuildFailed,
                r"project module B[.]Book crosses an unsafe source path",
            ):
                plan_reachable_project_modules(project, ("B.Book",))

    def test_reachable_plan_rejects_import_blocked_by_non_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            a_root = project / "Books" / "A"
            a_root.mkdir()
            (a_root / "Book.lean").write_text(
                "import B.Helper\n",
                encoding="utf-8",
            )
            (project / "Books" / "B").write_text("not a directory", encoding="utf-8")

            with self.assertRaisesRegex(
                BuildFailed,
                r"unresolved project import B[.]Helper crosses an unsafe source path",
            ):
                plan_reachable_project_modules(project, ("A.Book",))

    def test_unreferenced_symlink_directory_does_not_poison_external_imports(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            orphan = project / "Orphan"
            orphan.mkdir()
            (orphan / "Helper.lean").write_text("import Mathlib\n", encoding="utf-8")
            (project / "Books" / "OrphanLink").symlink_to(Path("../Orphan"))

            plan = plan_reachable_project_modules(project, ("Books.Demo.Book",))

            self.assertEqual(
                tuple(entry.name for entry in plan.entries),
                ("Books.Demo.Book", "Books.Demo.Chapter"),
            )

    def test_cross_project_owners_follow_each_selected_root_transitively(self) -> None:
        for b_imports_helper in (False, True):
            with self.subTest(b_imports_helper=b_imports_helper):
                with tempfile.TemporaryDirectory() as temp:
                    project = self._project(Path(temp), modern=True)
                    self._cross_project_sources(
                        project,
                        b_imports_helper=b_imports_helper,
                    )

                    plan = plan_reachable_project_modules(
                        project,
                        ("A.Book", "B.Book"),
                    )

                    expected_owners = {"A.Book"}
                    if b_imports_helper:
                        expected_owners.add("B.Book")
                    self.assertEqual(
                        plan.module_owners["B.Helper"],
                        frozenset(expected_owners),
                    )
                    self.assertEqual(
                        tuple(entry.name for entry in plan.entries).count("B.Helper"),
                        1,
                    )
                    self.assertEqual(
                        tuple(
                            tuple(entry.name for entry in batch)
                            for batch in plan.batches
                        ),
                        (("A.Book", "B.Helper"), ("B.Book",)),
                    )
                    self.assertNotIn("B.Orphan", plan.module_owners)

    def test_project_olean_candidates_cover_supported_lake_layouts(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            compiled = project / ".lake/build/lib/lean"
            source = project / "Books/Demo/Book.lean"

            aggregate = project_olean_candidates(
                project, compiled, "Books.Demo.Book", source
            )
            flat = project_olean_candidates(project, compiled, "Demo.Book", source)

            self.assertEqual(
                tuple(path.relative_to(compiled).as_posix() for path in aggregate),
                ("Books/Demo/Book.olean", "Demo/Book.olean"),
            )
            self.assertEqual(
                tuple(path.relative_to(compiled).as_posix() for path in flat),
                ("Demo/Book.olean", "Books/Demo/Book.olean"),
            )

    def test_project_olean_inspection_selects_each_supported_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            project = self._project(Path(temp), modern=True)
            compiled = project / ".lake/build/lib/lean"
            source = project / "Books/Demo/Book.lean"
            direct = compiled / "Demo/Book.olean"
            source_relative = compiled / "Books/Demo/Book.olean"

            direct.unlink()
            inspection = inspect_project_olean(project, compiled, "Demo.Book", source)
            self.assertTrue(inspection.succeeded)
            self.assertEqual(inspection.artifact, source_relative)

            source_relative.unlink()
            direct.parent.mkdir(parents=True, exist_ok=True)
            direct.write_bytes(b"stripped books prefix")
            inspection = inspect_project_olean(
                project, compiled, "Books.Demo.Book", source
            )
            self.assertTrue(inspection.succeeded)
            self.assertEqual(inspection.artifact, direct)

            inspection = inspect_project_olean(project, compiled, "Demo.Book", source)
            self.assertTrue(inspection.succeeded)
            self.assertEqual(inspection.artifact, direct)

    def test_project_olean_inspection_rejects_unsafe_preferred_candidate(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            compiled = project / ".lake/build/lib/lean"
            source = project / "Books/Demo/Book.lean"
            preferred = compiled / "Demo/Book.olean"
            fallback = compiled / "Books/Demo/Book.olean"
            outside = root / "outside.olean"
            outside.write_bytes(b"outside")

            for unsafe in ("empty", "directory", "symlink"):
                with self.subTest(unsafe=unsafe):
                    if preferred.is_dir() and not preferred.is_symlink():
                        preferred.rmdir()
                    else:
                        preferred.unlink(missing_ok=True)
                    if unsafe == "empty":
                        preferred.touch()
                    elif unsafe == "directory":
                        preferred.mkdir()
                    else:
                        preferred.symlink_to(outside)
                    self.assertGreater(fallback.stat().st_size, 0)

                    inspection = inspect_project_olean(
                        project, compiled, "Demo.Book", source
                    )

                    self.assertEqual(inspection.status, "unsafe")
                    self.assertFalse(inspection.succeeded)
                    self.assertIsNone(inspection.artifact)

    def test_modern_builder_closes_links_and_reuses_exact_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner()
            builder = ProjectDocumentationBuilder(runner=runner)
            output = root / "cache" / "docs"
            result = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertFalse(result.reused)
            self.assertEqual(result.mode, "database")
            self.assertEqual(result.targets, modules)
            self.assertEqual(
                tuple(
                    path.relative_to(output / "doc").as_posix() for path in result.pages
                ),
                ("Books/Demo/Book.html", "Books/Demo/Chapter.html"),
            )
            self.assertNotIn("Books.Demo.Dead", runner.modules)
            self.assertEqual(result.dependency_stubs, 1)
            libraries = [
                Path(value.removeprefix("--load-dynlib=")).name
                for value in runner.commands[0].argv
                if value.startswith("--load-dynlib=")
            ]
            self.assertEqual(
                libraries,
                [
                    "libleansqlite.so",
                    "leansqlite_SQLite_FFI.so",
                ],
            )
            stub = output / "doc" / "Mathlib" / "Dependency.html"
            self.assertIn("data-reasbook-doc-stub", stub.read_text(encoding="utf-8"))
            marker = json.loads(
                (output / "project-docs.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                marker["module_owners"],
                [
                    {
                        "module": "Books.Demo.Book",
                        "roots": ["Books.Demo.Book"],
                    },
                    {
                        "module": "Books.Demo.Chapter",
                        "roots": ["Books.Demo.Book"],
                    },
                ],
            )
            command_count = len(runner.commands)

            cached = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertTrue(cached.reused)
            self.assertEqual(len(runner.commands), command_count)

            chapter = project / "Books" / "Demo" / "Chapter.lean"
            chapter.write_text("import Mathlib\n-- changed\n", encoding="utf-8")
            rebuilt = builder.build(
                project,
                modules,
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            self.assertFalse(rebuilt.reused)
            self.assertGreater(len(runner.commands), command_count)

    def test_reference_statements_and_flat_contents_work_in_both_docgen_modes(self) -> None:
        for modern in (True, False):
            with self.subTest(modern=modern), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                project = self._project(root, modern=modern)
                (project / 'Books/Demo/Chapter.lean').write_text(
                    'import Mathlib\nvariable (n : Nat)\n/- A checked expression. -/\n#check n + 1\n'
                )
                output = root / 'output'
                runner = _DocsRunner()
                builder = ProjectDocumentationBuilder(runner=runner)
                builder.build(project, ('Books.Demo.Book',), output)
                chapter = (output / 'doc/Books/Demo/Chapter.html').read_text()
                self.assertIn('#check n + 1', chapter)
                self.assertIn('variable (n : Nat)', chapter)
                self.assertIn('A checked expression.', chapter)
                book = (output / 'doc/Books/Demo/Book.html').read_text()
                self.assertIn('href="Chapter.html"', book)
                self.assertNotIn('href="Dead.html"', book)
                self.assertTrue(builder.build(project, ('Books.Demo.Book',), output).reused)

    def test_statement_renderer_invalidates_html_but_reuses_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / 'output'
            ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                project, ('Books.Demo.Book',), output
            )
            marker = output / 'project-docs.json'
            old = json.loads(marker.read_text())
            old.pop('statement_renderer_sha256')
            marker.write_text(json.dumps(old))
            runner = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=runner).build(
                project, ('Books.Demo.Book',), output
            )
            self.assertFalse(result.reused)
            self.assertTrue(any('fromDb' in command.argv for command in runner.commands))
            self.assertFalse(any('--run' in command.argv for command in runner.commands))
            self.assertIn('statement_renderer_sha256', json.loads(marker.read_text()))

    def test_reference_metadata_invalidates_html_without_repeating_analysis(self) -> None:
        for modern in (True, False):
            with self.subTest(modern=modern), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                project = self._project(root, modern=modern)
                (project / 'Books/Demo/Chapter.lean').write_text('import Mathlib\n#check Nat.succ\n')
                output = root / 'output'
                builder = ProjectDocumentationBuilder(runner=_DocsRunner())
                builder.build(project, ('Books.Demo.Book',), output)
                page = output / 'doc/Books/Demo/Chapter.html'
                self.assertNotIn('statement-reference', page.read_text())
                metadata = project / '.lake/build/lib/lean/Books/Demo/Chapter.ilean'

                def write_metadata(owner):
                    metadata.write_text(json.dumps({
                        'version': 5 if modern else 4, 'module': 'Books.Demo.Chapter',
                        'references': {json.dumps({'c': {'m': owner, 'n': 'Nat.succ'}}):
                                       {'definition': None, 'usages': [[1, 7, 1, 15]]}},
                    }))

                write_metadata('Init.Prelude')
                for owner in ('Init.Prelude', 'Init.Data.Nat.Basic'):
                    write_metadata(owner)
                    runner = _DocsRunner()
                    builder = ProjectDocumentationBuilder(runner=runner)
                    result = builder.build(project, ('Books.Demo.Book',), output)
                    self.assertFalse(result.reused)
                    self.assertIn(owner.replace('.', '/') + '.html#Nat.succ', page.read_text())
                    if modern:
                        self.assertFalse(any('--run' in command.argv for command in runner.commands))
                    self.assertTrue(builder.build(project, ('Books.Demo.Book',), output).reused)
                metadata.unlink()
                self.assertFalse(builder.build(project, ('Books.Demo.Book',), output).reused)
                self.assertNotIn('statement-reference', page.read_text())

    def test_reference_metadata_symlink_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            source = project / 'Books/Demo/Chapter.lean'
            source.write_text('#check Nat.succ\n')
            outside = root / 'outside.ilean'
            outside.write_text('{}')
            metadata = project / '.lake/build/lib/lean/Books/Demo/Chapter.ilean'
            metadata.symlink_to(outside)
            with self.assertRaisesRegex(BuildFailed, 'unsafe reference metadata'):
                ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                    project, ('Books.Demo.Book',), root / 'output')

    def test_metadata_changed_during_render_does_not_replace_published_docs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            (project / 'Books/Demo/Chapter.lean').write_text('import Mathlib\n#check Nat.succ\n')
            metadata = project / '.lake/build/lib/lean/Books/Demo/Chapter.ilean'
            metadata.write_text('{}')
            output = root / 'output'
            ProjectDocumentationBuilder(runner=_DocsRunner()).build(project, ('Books.Demo.Book',), output)
            page = output / 'doc/Books/Demo/Chapter.html'
            original = page.read_bytes()
            metadata.write_text('{"version": 999}')

            class MutatingRunner(_DocsRunner):
                def run(self, command):
                    result = super().run(command)
                    if 'fromDb' in command.argv:
                        metadata.write_text('{}')
                    return result

            with self.assertRaisesRegex(BuildFailed, 'reference metadata changed'):
                ProjectDocumentationBuilder(runner=MutatingRunner()).build(
                    project, ('Books.Demo.Book',), output)
            self.assertEqual(page.read_bytes(), original)

    def test_compiled_artifact_changes_invalidate_docs_and_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"

            first = _DocsRunner()
            ProjectDocumentationBuilder(runner=first).build(
                project, ("Books.Demo.Book",), output
            )
            first_identity = json.loads(
                (output / "project-docs.json").read_text(encoding="utf-8")
            )["compiled_artifacts"]

            changes = (
                project
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "Books"
                / "Demo"
                / "Chapter.olean",
                self._package_lib(project, "leansqlite") / "libleansqlite.so",
            )
            previous = first_identity
            for artifact in changes:
                with self.subTest(artifact=artifact):
                    original = artifact.read_bytes()
                    replacement = bytes(byte ^ 1 for byte in original)
                    artifact.write_bytes(replacement)
                    runner = _DocsRunner()
                    result = ProjectDocumentationBuilder(runner=runner).build(
                        project, ("Books.Demo.Book",), output
                    )
                    current = json.loads(
                        (output / "project-docs.json").read_text(encoding="utf-8")
                    )["compiled_artifacts"]
                    self.assertFalse(result.reused)
                    self.assertNotEqual(current["sha256"], previous["sha256"])
                    self.assertTrue(
                        any("--run" in command.argv for command in runner.commands)
                    )
                    previous = current

    def test_database_connections_close_before_documentation_publication(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"
            connections: list[_TrackingConnection] = []
            connect = sqlite3.connect

            def tracked_connect(*args, **kwargs):
                kwargs["factory"] = _TrackingConnection
                connection = connect(*args, **kwargs)
                connections.append(connection)
                return connection

            with patch.object(sqlite3, "connect", side_effect=tracked_connect):
                ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                    project, ("Books.Demo.Book",), output
                )

            self.assertGreater(len(connections), 0)
            self.assertTrue(all(connection.was_closed for connection in connections))
            self.assertEqual(
                [
                    path
                    for path in output.rglob("*")
                    if path.name.endswith(("-wal", "-shm"))
                ],
                [],
            )

    def test_unmanaged_metadata_cannot_suppress_dependency_hashing(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            manifest = project / "lake-manifest.json"
            manifest.write_text('{"version": 1}\n', encoding="utf-8")
            dependency = self._write_olean(
                project / ".lake" / "packages" / "Dependency",
                "Dependency.Module",
                b"dependency olean",
            )
            metadata = {
                "schema": 1,
                "branch": "v4.30.0",
                "commit": "a" * 40,
                "manifest_sha256": ProjectDocumentationBuilder._sha256(manifest),
                "toolchain": "v4.30.0",
                "architecture": platform.machine() or "unknown",
            }
            (project / ".lake" / "cache-metadata.json").write_text(
                json.dumps(metadata), encoding="utf-8"
            )
            batches, _owners = ProjectDocumentationBuilder._module_plan(
                project, ("Books.Demo.Book",)
            )
            sources = tuple(item for batch in batches for item in batch)
            docgen = (
                project
                / ".lake"
                / "packages"
                / "doc-gen4"
                / ".lake"
                / "build"
                / "bin"
                / "doc-gen4"
            ).resolve()

            before = ProjectDocumentationBuilder._compiled_artifact_identity(
                project, sources, docgen, revision="a" * 40
            )
            dependency.write_bytes(b"changed artifact")
            after = ProjectDocumentationBuilder._compiled_artifact_identity(
                project, sources, docgen, revision="a" * 40
            )

            self.assertIsNone(before["branch_cache"])
            self.assertIsNone(after["branch_cache"])
            self.assertNotEqual(before["sha256"], after["sha256"])

    def test_managed_cache_requires_exact_namespace_and_host_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            manifest = project / "lake-manifest.json"
            manifest.write_text('{"version": 1}\n', encoding="utf-8")
            digest = ProjectDocumentationBuilder._sha256(manifest)
            branch = "v4.30.0"
            commit = "a" * 40
            toolchain = "v4.30.0"
            architecture = platform.machine() or "unknown"
            namespace = (
                f"branch-{branch}-{commit[:12]}-{digest[:16]}-"
                f"{toolchain}-{architecture}"
            )
            cache_parent = root / "managed" / "lake"
            cache_parent.mkdir(parents=True)
            cache = cache_parent / namespace
            (project / ".lake").rename(cache)
            (project / ".lake").symlink_to(cache, target_is_directory=True)
            metadata_path = cache / "cache-metadata.json"
            metadata = {
                "schema": 1,
                "branch": branch,
                "commit": commit,
                "manifest_sha256": digest,
                "toolchain": toolchain,
                "architecture": architecture,
            }
            metadata_path.write_text(json.dumps(metadata), encoding="utf-8")

            identity = ProjectDocumentationBuilder._managed_branch_cache_identity(
                project, project / ".lake", revision=commit
            )

            self.assertEqual(identity["purpose"], "release-branch-build")
            self.assertEqual(identity["namespace"], namespace)
            mutations = (
                {**metadata, "toolchain": "v4.29.0"},
                {**metadata, "architecture": "wrong-host"},
                {**metadata, "branch": "other-branch"},
                {**metadata, "purpose": "release-finalizer-web"},
            )
            for value in mutations:
                with self.subTest(value=value):
                    metadata_path.write_text(json.dumps(value), encoding="utf-8")
                    with self.assertRaises(BuildFailed):
                        ProjectDocumentationBuilder._managed_branch_cache_identity(
                            project, project / ".lake", revision=commit
                        )

    def test_managed_project_cache_requires_exact_finalizer_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            cache, _branch, finalizer, namespace, _configuration = (
                self._managed_finalizer_cache(root, project)
            )

            identity = ProjectDocumentationBuilder._managed_branch_cache_identity(
                project, project / ".lake", revision="a" * 40
            )

            self.assertEqual(identity["namespace"], namespace)
            self.assertEqual(identity["project_key"], "books/Demo")
            marker = cache / "finalizer-cache.json"
            mutations = (
                {**finalizer, "project_key": "papers/Demo"},
                {**finalizer, "tooling_sha256": "c" * 64},
                {**finalizer, "seed_namespace": f"{namespace}-other"},
                {**finalizer, "build_configuration_sha256": "d" * 64},
                {**finalizer, "purpose": "release-finalizer-web"},
                {**finalizer, "unexpected": True},
            )
            for value in mutations:
                with self.subTest(value=value):
                    marker.write_text(json.dumps(value), encoding="utf-8")
                    with self.assertRaises(BuildFailed):
                        ProjectDocumentationBuilder._managed_branch_cache_identity(
                            project, project / ".lake", revision="a" * 40
                        )

            marker.write_bytes(b" " * (1024 * 1024 + 1))
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._managed_branch_cache_identity(
                    project, project / ".lake", revision="a" * 40
                )

            marker.write_text(json.dumps(finalizer), encoding="utf-8")
            external_marker = root / "external-finalizer-cache.json"
            external_marker.write_text(json.dumps(finalizer), encoding="utf-8")
            marker.unlink()
            marker.symlink_to(external_marker)
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._managed_branch_cache_identity(
                    project, project / ".lake", revision="a" * 40
                )

    def test_managed_project_cache_rejects_noncanonical_layouts(self) -> None:
        for mutation in ("projects-component", "configuration-digest"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                project = self._project(root, modern=True)
                cache, _branch, _finalizer, _namespace, _configuration = (
                    self._managed_finalizer_cache(root, project)
                )
                lake = project / ".lake"
                lake.unlink()
                if mutation == "projects-component":
                    parent = cache.parent
                    replacement = parent.with_name("project")
                    parent.rename(replacement)
                    cache = replacement / cache.name
                else:
                    configuration = cache.parents[3]
                    replacement = configuration.with_name(f"cfg-{'e' * 64}")
                    relative = cache.relative_to(configuration)
                    configuration.rename(replacement)
                    cache = replacement / relative
                lake.symlink_to(cache, target_is_directory=True)

                with self.assertRaises(BuildFailed):
                    ProjectDocumentationBuilder._managed_branch_cache_identity(
                        project, lake, revision="a" * 40
                    )

    def test_managed_project_cache_hashes_ordinary_dependency_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            self._managed_finalizer_cache(root, project)
            dependency = self._write_olean(
                project / ".lake" / "packages" / "Dependency",
                "Dependency.Module",
                b"dependency olean",
            )
            batches, _owners = ProjectDocumentationBuilder._module_plan(
                project, ("Books.Demo.Book",)
            )
            sources = tuple(item for batch in batches for item in batch)
            docgen = (
                project
                / ".lake"
                / "packages"
                / "doc-gen4"
                / ".lake"
                / "build"
                / "bin"
                / "doc-gen4"
            ).resolve()

            before = ProjectDocumentationBuilder._compiled_artifact_identity(
                project, sources, docgen, revision="a" * 40
            )
            dependency.write_bytes(b"changed dependency olean")
            after = ProjectDocumentationBuilder._compiled_artifact_identity(
                project, sources, docgen, revision="a" * 40
            )

            self.assertEqual(before["branch_cache"]["project_key"], "books/Demo")
            self.assertEqual(after["branch_cache"]["project_key"], "books/Demo")
            self.assertNotEqual(before["sha256"], after["sha256"])

    def test_managed_branch_finalizer_hashes_ordinary_dependencies(self) -> None:
        for configured in (False, True):
            with self.subTest(
                configured=configured
            ), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                project = self._project(root, modern=True)
                self._managed_finalizer_cache(
                    root,
                    project,
                    project_key=None,
                    configured=configured,
                )
                dependency = self._write_olean(
                    project / ".lake" / "packages" / "Dependency",
                    "Dependency.Module",
                    b"dependency olean",
                )
                batches, _owners = ProjectDocumentationBuilder._module_plan(
                    project, ("Books.Demo.Book",)
                )
                sources = tuple(item for batch in batches for item in batch)
                docgen = (
                    project
                    / ".lake"
                    / "packages"
                    / "doc-gen4"
                    / ".lake"
                    / "build"
                    / "bin"
                    / "doc-gen4"
                ).resolve()

                managed = ProjectDocumentationBuilder._managed_lake_cache_identity(
                    project, project / ".lake", revision="a" * 40
                )
                before = ProjectDocumentationBuilder._compiled_artifact_identity(
                    project, sources, docgen, revision="a" * 40
                )
                dependency.write_bytes(b"changed dependency olean")
                after = ProjectDocumentationBuilder._compiled_artifact_identity(
                    project, sources, docgen, revision="a" * 40
                )

                self.assertEqual(
                    managed.value["policy"],
                    "validated-writable-branch-finalizer-cache-v1",
                )
                self.assertFalse(managed.dependency_artifacts_are_immutable)
                self.assertNotEqual(before["sha256"], after["sha256"])

    def test_legacy_builder_uses_bounded_adapter_then_index(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            modules = ("Books.Demo.Book",)
            runner = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                modules,
                root / "cache" / "docs",
            )
            self.assertEqual(result.mode, "legacy")
            verbs = [
                "batch" if "--run" in command.argv else "index"
                for command in runner.commands
            ]
            self.assertEqual(verbs, ["batch", "index"])
            adapter = runner.commands[0].argv
            lean = adapter.index("lean")
            self.assertEqual(adapter[lean + 1 : lean + 3], ("-j", "1"))
            libraries = [
                value.removeprefix("--load-dynlib=")
                for value in adapter
                if value.startswith("--load-dynlib=")
            ]
            self.assertEqual(
                [Path(value).name for value in libraries],
                ["libUnicodeBasic.so", "libleanmd4c.so", "libMD4Lean.so"],
            )

    def test_legacy_adapter_accepts_scoped_aggregate_library_names(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            unicode_root = self._package_lib(project, "UnicodeBasic")
            (unicode_root / "libUnicodeBasic.so").rename(
                unicode_root / "libUnicodeBasic_UnicodeBasic.so"
            )
            md4lean_root = self._package_lib(project, "MD4Lean")
            (md4lean_root / "libMD4Lean.so").rename(
                md4lean_root / "libMD4Lean_MD4Lean.so"
            )

            arguments = ProjectDocumentationBuilder._legacy_interpreter_args(project)

            self.assertEqual(
                [
                    Path(value.removeprefix("--load-dynlib=")).name
                    for value in arguments
                ],
                [
                    "libUnicodeBasic_UnicodeBasic.so",
                    "libleanmd4c.so",
                    "libMD4Lean_MD4Lean.so",
                ],
            )

    def test_legacy_adapter_rejects_ambiguous_unicode_aggregates(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            library_root = self._package_lib(project, "UnicodeBasic")
            (library_root / "libUnicodeBasic_UnicodeBasic.so").write_bytes(
                b"stale fixture"
            )

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._legacy_interpreter_args(project)

    def test_legacy_adapter_rejects_symlinked_unicode_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            library = self._package_lib(project, "UnicodeBasic") / "libUnicodeBasic.so"
            target = library.with_name("external-unicode.so")
            library.rename(target)
            library.symlink_to(target)

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._legacy_interpreter_args(project)

    def test_legacy_adapter_rejects_empty_unicode_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            library = self._package_lib(project, "UnicodeBasic") / "libUnicodeBasic.so"
            library.write_bytes(b"")

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._legacy_interpreter_args(project)

    def test_legacy_adapter_rejects_ambiguous_md4lean_aggregates(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            library_root = self._package_lib(project, "MD4Lean")
            (library_root / "libMD4Lean_MD4Lean.so").write_bytes(b"stale fixture")

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._legacy_interpreter_args(project)

    def test_legacy_adapter_requires_md4lean_c_provider(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            provider = self._package_lib(project, "MD4Lean") / "libleanmd4c.so"
            provider.unlink()

            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder._legacy_interpreter_args(project)

    def test_flat_layout_discovers_project_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            book = project / "Books" / "Demo" / "Book.lean"
            book.write_text("import Demo.Chapter\n", encoding="utf-8")
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Demo.Book",),
                root / "cache" / "docs-flat",
            )

            self.assertEqual(result.targets, ("Demo.Book",))
            self.assertEqual(runner.modules, ["Demo.Book", "Demo.Chapter"])

    def test_large_project_is_split_into_bounded_analyzer_batches(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            module_root = project / "Books" / "Demo"
            names = [f"Books.Demo.Part{index:03d}" for index in range(130)]
            (module_root / "Book.lean").write_text(
                "\n".join(f"import {name}" for name in names) + "\n",
                encoding="utf-8",
            )
            for index in range(130):
                (module_root / f"Part{index:03d}.lean").write_text(
                    "import Mathlib\n",
                    encoding="utf-8",
                )
                self._write_olean(project, f"Books.Demo.Part{index:03d}")
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Books.Demo.Book",),
                root / "cache" / "docs-batched",
            )

            adapter_commands = [
                command for command in runner.commands if "--run" in command.argv
            ]
            self.assertEqual(len(result.pages), 131)
            self.assertEqual(len(adapter_commands), 2)
            for command in adapter_commands:
                lean = command.argv.index("lean")
                self.assertEqual(command.argv[lean + 1 : lean + 3], ("-j", "1"))

    def test_local_lean_link_is_pinned_by_unique_reachable_owner(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "ReasBook"
            sources = (
                (
                    "BookA.Chap05.Current",
                    project / "Books" / "BookA" / "Chap05" / "Current.lean",
                ),
                (
                    "BookA.Chap04.Shared",
                    project / "Books" / "BookA" / "Chap04" / "Shared.lean",
                ),
                (
                    "BookB.Chap04.Shared",
                    project / "Books" / "BookB" / "Chap04" / "Shared.lean",
                ),
            )
            for _module, source in sources:
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("import Mathlib\n", encoding="utf-8")
            sources[0][1].write_text(
                "import Mathlib\n-- /old/BookA/Items/Chap04/Shared.lean\n",
                encoding="utf-8",
            )
            owners = {
                "BookA.Chap05.Current": frozenset({"BookA.Book"}),
                "BookA.Chap04.Shared": frozenset({"BookA.Book"}),
                "BookB.Chap04.Shared": frozenset({"BookB.Book"}),
            }
            doc = root / "docs" / "doc"
            page = doc / "BookA" / "Chap05" / "Current.html"
            page.parent.mkdir(parents=True)
            (doc / "style.css").write_text("body{}", encoding="utf-8")
            doc.joinpath("index.html").write_text(
                "<html>index</html>", encoding="utf-8"
            )
            stale = "../.././/old/BookA/Items/Chap04/Shared.lean"
            encoded = stale.replace(".lean", "&#46;lean")
            page.write_text(
                f"<html><body><a data-note=\" href='{stale}'\"\n"
                f" href='{stale}' href=\"{encoded}\">source</a>"
                f"<a href={stale}>bare</a>"
                f"<script>const untouched = 'href=\"{stale}\"';</script>"
                "</body></html>",
                encoding="utf-8",
            )

            ProjectDocumentationBuilder._close_documentation_links(
                doc,
                project_root=project,
                module_sources=sources,
                module_owners=owners,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )

            content = page.read_text(encoding="utf-8")
            expected = (
                "https://github.com/acme/reasbook/blob/"
                + "a" * 40
                + "/ReasBook/Books/BookA/Chap04/Shared.lean"
            )
            self.assertEqual(content.count(expected), 3)
            self.assertIn(f"data-note=\" href='{stale}'\"", content)
            self.assertIn(f"const untouched = 'href=\"{stale}\"'", content)

    def test_unspanned_or_unsafe_internal_links_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "ReasBook"
            source = project / "Books" / "BookA" / "Current.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Mathlib\n", encoding="utf-8")
            cases = (
                ('<a = href="missing.png">malformed</a>', "safely locate"),
                ('<img src="missing\\asset.png">', "unsafe path"),
                ('<a href="C:\\missing.lean">windows</a>', "unsafe scheme"),
                ('<a href="C:/missing.lean">windows</a>', "unsafe scheme"),
                ('<a href="%43%3A%2Fmissing.lean">windows</a>', "unsafe path"),
                ('<img src="missing%00asset.png">', "unsafe path"),
                ('<a href="file:///tmp/missing.lean">file</a>', "unsafe scheme"),
                (
                    '<a href="file://localhost/tmp/missing.lean">file</a>',
                    "unsafe scheme",
                ),
                ('<a href="ftp://example.com/missing.lean">ftp</a>', "unsafe scheme"),
                (
                    '<a href="//example.com/missing.lean">network</a>',
                    "protocol-relative",
                ),
            )
            for sequence, (markup, error) in enumerate(cases):
                with self.subTest(markup=markup):
                    doc = root / f"unsafe-{sequence}" / "doc"
                    doc.mkdir(parents=True)
                    (doc / "style.css").write_text("body{}", encoding="utf-8")
                    (doc / "index.html").write_text(
                        f"<html>{markup}</html>", encoding="utf-8"
                    )
                    with self.assertRaisesRegex(BuildFailed, error):
                        ProjectDocumentationBuilder._close_documentation_links(
                            doc,
                            project_root=project,
                            module_sources=(("BookA.Current", source),),
                            module_owners={"BookA.Current": frozenset({"BookA.Book"})},
                            repository="https://github.com/acme/reasbook",
                            revision="a" * 40,
                        )

    def test_base_element_cannot_redirect_link_closure(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "ReasBook"
            source = project / "Books" / "BookA" / "Current.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Mathlib\n", encoding="utf-8")
            cases = (
                '<base href="https://evil.example/">',
                '<base href="../outside/">',
                '<base href=""><base href="">',
                '<base href="" href="">',
            )
            for sequence, base in enumerate(cases):
                with self.subTest(base=base):
                    doc = root / f"base-{sequence}" / "doc"
                    doc.mkdir(parents=True)
                    (doc / "style.css").write_text("body{}", encoding="utf-8")
                    (doc / "index.html").write_text(
                        f"<html><head>{base}</head>"
                        '<body><img src="missing.png"></body></html>',
                        encoding="utf-8",
                    )
                    with self.assertRaisesRegex(BuildFailed, "base element"):
                        ProjectDocumentationBuilder._close_documentation_links(
                            doc,
                            project_root=project,
                            module_sources=(("BookA.Current", source),),
                            module_owners={"BookA.Current": frozenset({"BookA.Book"})},
                            repository="https://github.com/acme/reasbook",
                            revision="a" * 40,
                        )

    def test_missing_stylesheet_prevents_stub_publication(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "ReasBook"
            source = project / "Books" / "BookA" / "Current.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Mathlib\n", encoding="utf-8")
            doc = root / "docs" / "doc"
            doc.mkdir(parents=True)
            (doc / "index.html").write_text(
                '<html><a href="Mathlib/Missing.html">dependency</a></html>',
                encoding="utf-8",
            )

            with self.assertRaisesRegex(BuildFailed, "style.css"):
                ProjectDocumentationBuilder._close_documentation_links(
                    doc,
                    project_root=project,
                    module_sources=(("BookA.Current", source),),
                    module_owners={"BookA.Current": frozenset({"BookA.Book"})},
                    repository="https://github.com/acme/reasbook",
                    revision="a" * 40,
                )

            self.assertFalse((doc / "Mathlib" / "Missing.html").exists())

    def test_repository_url_is_strict_and_canonical(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            invalid = (
                'https://github.com/acme/repo" onmouseover="alert(1)',
                "https://github.com/acme/repo?download=1",
                "https://github.com/acme/repo#fragment",
                "https://github.com/acme/repo%2Fextra",
                "https://github.com/acme/repo%22onclick",
                "https://user@github.com/acme/repo",
                "https://github.com:443/acme/repo",
                "https://github.com/acme/repo/extra",
                " https://github.com/acme/repo",
            )
            for sequence, repository in enumerate(invalid):
                with self.subTest(repository=repository):
                    with self.assertRaises(ConfigurationError):
                        ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                            project,
                            ("Books.Demo.Book",),
                            root / f"invalid-repository-{sequence}",
                            repository=repository,
                            revision="a" * 40,
                        )

            output = root / "canonical-repository"
            ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                project,
                ("Books.Demo.Book",),
                output,
                repository="https://github.com/acme/reasbook.git",
                revision="a" * 40,
            )
            marker = json.loads(
                (output / "project-docs.json").read_text(encoding="utf-8")
            )
            self.assertEqual(marker["repository"], "https://github.com/acme/reasbook")

    def test_output_symlinks_are_rejected_before_canonicalization(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            external = root / "external"
            external.mkdir()
            (external / "sentinel.txt").write_text("unchanged", encoding="utf-8")
            direct = root / "direct-output"
            direct.symlink_to(external, target_is_directory=True)
            parent = root / "linked-parent"
            parent.symlink_to(external, target_is_directory=True)

            for output in (direct, parent / "nested-output"):
                with self.subTest(output=output):
                    runner = _DocsRunner()
                    with self.assertRaisesRegex(ConfigurationError, "symlink"):
                        ProjectDocumentationBuilder(runner=runner).build(
                            project,
                            ("Books.Demo.Book",),
                            output,
                        )
                    self.assertEqual(runner.commands, [])
                    self.assertEqual(
                        sorted(path.name for path in external.iterdir()),
                        ["sentinel.txt"],
                    )

    def test_unknown_or_ambiguous_lean_links_remain_hard_failures(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "ReasBook"
            sources = (
                ("BookA.Current", project / "Books" / "BookA" / "Current.lean"),
                (
                    "BookA.Chap04.Shared",
                    project / "Books" / "BookA" / "Chap04" / "Shared.lean",
                ),
                (
                    "BookB.Chap04.Shared",
                    project / "Books" / "BookB" / "Chap04" / "Shared.lean",
                ),
            )
            for _module, source in sources:
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("import Mathlib\n", encoding="utf-8")
            sources[0][1].write_text(
                "import Mathlib\n"
                "-- /old/Chap04/Shared.lean\n"
                "-- /old/Chap04/Unknown.lean\n",
                encoding="utf-8",
            )
            owners = {module: frozenset({"Combined.Book"}) for module, _ in sources}
            references = (
                "/old/Chap04/Shared.lean",
                "/old/Chap04/Unknown.lean",
                "missing.png",
            )
            for sequence, reference in enumerate(references):
                with self.subTest(reference=reference):
                    doc = root / f"docs-{sequence}" / "doc"
                    page = doc / "BookA" / "Current.html"
                    page.parent.mkdir(parents=True)
                    (doc / "style.css").write_text("body{}", encoding="utf-8")
                    (doc / "index.html").write_text(
                        "<html>index</html>", encoding="utf-8"
                    )
                    page.write_text(
                        f'<html><a href="{reference}">missing</a></html>',
                        encoding="utf-8",
                    )

                    with self.assertRaisesRegex(BuildFailed, re.escape(reference)):
                        ProjectDocumentationBuilder._close_documentation_links(
                            doc,
                            project_root=project,
                            module_sources=sources,
                            module_owners=owners,
                            repository="https://github.com/acme/reasbook",
                            revision="a" * 40,
                        )

    def test_failed_render_reuses_content_addressed_analysis_checkpoint(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"
            first = _BrokenRenderRunner()
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder(runner=first).build(
                    project,
                    ("Books.Demo.Book",),
                    output,
                    repository="https://github.com/acme/reasbook",
                    revision="a" * 40,
                )
            self.assertFalse(output.exists())
            checkpoints = list(
                output.parent.glob(".project-docs-analysis-v1/*/analysis.json")
            )
            self.assertEqual(len(checkpoints), 1)
            self.assertEqual(
                {path.name for path in checkpoints[0].parent.iterdir()},
                {"analysis.json", "api-docs.db"},
            )
            checkpoint_database = checkpoints[0].parent / "api-docs.db"
            with sqlite3.connect(
                checkpoint_database.resolve().as_uri() + "?mode=ro&immutable=1",
                uri=True,
            ) as connection:
                self.assertEqual(
                    connection.execute("PRAGMA journal_mode").fetchone(),
                    ("delete",),
                )
            checkpoint_payload = json.loads(checkpoints[0].read_text(encoding="utf-8"))
            database_schema = checkpoint_payload["database_schema"]
            self.assertEqual(
                database_schema["schema_meta"],
                {"ddl_hash": "fixture-ddl", "type_hash": "fixture-types"},
            )
            self.assertEqual(
                set(database_schema["required_tables"]),
                docs_module._ANALYZER_REQUIRED_TABLES,
            )
            self.assertRegex(database_schema["sqlite_schema_sha256"], r"^[0-9a-f]{64}$")

            second = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=second).build(
                project,
                ("Books.Demo.Book",),
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )

            self.assertFalse(result.reused)
            self.assertFalse(
                any("--run" in command.argv for command in second.commands)
            )
            self.assertEqual(len(second.commands), 1)
            self.assertIn("fromDb", second.commands[0].argv)

    def test_checkpoint_schema_tamper_forces_fresh_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder(runner=_BrokenRenderRunner()).build(
                    project, ("Books.Demo.Book",), output
                )
            marker = next(
                output.parent.glob(".project-docs-analysis-v1/*/analysis.json")
            )
            database = marker.parent / "api-docs.db"
            with sqlite3.connect(database) as connection:
                connection.execute("DROP TABLE tactics")
            payload = json.loads(marker.read_text(encoding="utf-8"))
            payload["database_bytes"] = database.stat().st_size
            payload["database_sha256"] = ProjectDocumentationBuilder._sha256(database)
            marker.write_text(json.dumps(payload), encoding="utf-8")

            runner = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=runner).build(
                project, ("Books.Demo.Book",), output
            )

            self.assertFalse(result.reused)
            self.assertTrue(any("--run" in command.argv for command in runner.commands))

    def test_checkpoint_schema_metadata_tamper_forces_fresh_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder(runner=_BrokenRenderRunner()).build(
                    project, ("Books.Demo.Book",), output
                )
            marker = next(
                output.parent.glob(".project-docs-analysis-v1/*/analysis.json")
            )
            database = marker.parent / "api-docs.db"
            with sqlite3.connect(database) as connection:
                connection.execute(
                    "UPDATE schema_meta SET value = ? WHERE key = 'ddl_hash'",
                    ("tampered-ddl",),
                )
            payload = json.loads(marker.read_text(encoding="utf-8"))
            payload["database_bytes"] = database.stat().st_size
            payload["database_sha256"] = ProjectDocumentationBuilder._sha256(database)
            marker.write_text(json.dumps(payload), encoding="utf-8")

            runner = _DocsRunner()
            result = ProjectDocumentationBuilder(runner=runner).build(
                project, ("Books.Demo.Book",), output
            )

            self.assertFalse(result.reused)
            self.assertTrue(any("--run" in command.argv for command in runner.commands))

    def test_restored_render_failure_retries_fresh_analysis_once(self) -> None:
        for always_fail in (False, True):
            with self.subTest(always_fail=always_fail):
                with tempfile.TemporaryDirectory() as temp:
                    root = Path(temp)
                    project = self._project(root, modern=True)
                    output = root / "cache" / "docs"
                    with self.assertRaises(BuildFailed):
                        ProjectDocumentationBuilder(runner=_BrokenRenderRunner()).build(
                            project, ("Books.Demo.Book",), output
                        )
                    checkpoint_marker = next(
                        output.parent.glob(".project-docs-analysis-v1/*/analysis.json")
                    )
                    before = checkpoint_marker.read_bytes()
                    runner = _CommandRenderFailureRunner(always=always_fail)

                    if always_fail:
                        with self.assertRaises(BuildFailed):
                            ProjectDocumentationBuilder(runner=runner).build(
                                project, ("Books.Demo.Book",), output
                            )
                        self.assertFalse(output.exists())
                        self.assertEqual(checkpoint_marker.read_bytes(), before)
                    else:
                        result = ProjectDocumentationBuilder(runner=runner).build(
                            project, ("Books.Demo.Book",), output
                        )
                        self.assertFalse(result.reused)

                    analyzer_count = sum(
                        "--run" in command.argv for command in runner.commands
                    )
                    self.assertEqual(runner.render_attempts, 2)
                    self.assertEqual(analyzer_count, 1)

    def test_non_object_analysis_marker_is_a_cache_miss(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            checkpoint = Path(temp) / "checkpoint"
            checkpoint.mkdir()
            (checkpoint / "api-docs.db").write_bytes(b"invalid fixture")
            marker = checkpoint / "analysis.json"
            for payload in ("[]", '"invalid"', "null"):
                with self.subTest(payload=payload):
                    marker.write_text(payload, encoding="utf-8")
                    self.assertFalse(
                        ProjectDocumentationBuilder._valid_analysis_checkpoint(
                            checkpoint, {}, ()
                        )
                    )

    def test_corrupt_analysis_database_is_a_cache_miss(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            checkpoint = Path(temp) / "checkpoint"
            checkpoint.mkdir()
            database = checkpoint / "api-docs.db"
            database.write_bytes(b"not a sqlite database")
            marker = {
                "schema_version": 1,
                "identity": {},
                "database_bytes": database.stat().st_size,
                "database_sha256": ProjectDocumentationBuilder._sha256(database),
                "database_schema": {},
            }
            (checkpoint / "analysis.json").write_text(
                json.dumps(marker), encoding="utf-8"
            )

            self.assertFalse(
                ProjectDocumentationBuilder._valid_analysis_checkpoint(
                    checkpoint, {}, ()
                )
            )

    def test_checkpoint_replacement_failure_restores_previous_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            output = root / "cache" / "docs"
            with self.assertRaises(BuildFailed):
                ProjectDocumentationBuilder(runner=_BrokenRenderRunner()).build(
                    project, ("Books.Demo.Book",), output
                )
            marker = next(
                output.parent.glob(".project-docs-analysis-v1/*/analysis.json")
            )
            checkpoint = marker.parent
            before = marker.read_bytes()
            payload = json.loads(before)
            identity = payload["identity"]
            modules = tuple(identity["modules"])
            candidate = root / "candidate.db"
            ProjectDocumentationBuilder._backup_analysis_database(
                checkpoint / "api-docs.db", candidate
            )
            real_replace = docs_module.os.replace
            calls = 0

            def fail_checkpoint_publication(source, destination):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise OSError("simulated checkpoint publication failure")
                return real_replace(source, destination)

            with patch(
                "reasbook_build_sdk.docs.os.replace",
                side_effect=fail_checkpoint_publication,
            ):
                with self.assertRaises(OSError):
                    ProjectDocumentationBuilder._store_analysis_checkpoint(
                        checkpoint,
                        candidate,
                        identity,
                        modules,
                        replace_existing=True,
                    )

            self.assertEqual(marker.read_bytes(), before)
            self.assertTrue(
                ProjectDocumentationBuilder._valid_analysis_checkpoint(
                    checkpoint, identity, modules
                )
            )
            self.assertEqual(
                list(checkpoint.parent.glob(f".{checkpoint.name}.stage-*")), []
            )
            self.assertEqual(
                list(checkpoint.parent.glob(f".{checkpoint.name}.backup-*")), []
            )

    def test_pre_policy_cache_is_migrated_atomically_without_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            (project / "Books" / "Demo" / "Book.lean").write_text(
                "import Mathlib\nimport Books.Demo.Chapter\n"
                "-- /old/Demo/Chapter.lean\n",
                encoding="utf-8",
            )
            output = root / "cache" / "docs"
            builder = ProjectDocumentationBuilder(runner=_DocsRunner())
            builder.build(
                project,
                ("Books.Demo.Book",),
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )
            marker = output / "project-docs.json"
            legacy = json.loads(marker.read_text(encoding="utf-8"))
            legacy.pop("link_policy")
            marker.write_text(json.dumps(legacy), encoding="utf-8")
            page = output / "doc" / "Books" / "Demo" / "Book.html"
            content = page.read_text(encoding="utf-8")
            page.write_text(
                content.replace(
                    "</body>",
                    '<a href="../.././/old/Demo/Chapter.lean">source</a></body>',
                ),
                encoding="utf-8",
            )
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Books.Demo.Book",),
                output,
                repository="https://github.com/acme/reasbook",
                revision="a" * 40,
            )

            self.assertTrue(result.reused)
            self.assertEqual(runner.commands, [])
            upgraded = json.loads(marker.read_text(encoding="utf-8"))
            self.assertEqual(upgraded["link_policy"]["schema_version"], 1)
            self.assertIn(
                "https://github.com/acme/reasbook/blob/"
                + "a" * 40
                + "/ReasBook/Books/Demo/Chapter.lean",
                page.read_text(encoding="utf-8"),
            )
            self.assertEqual(list(output.parent.glob(".docs.migration-*")), [])

    def test_explicit_root_includes_only_reachable_sibling_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=True)
            papers = project / "Papers"
            papers.mkdir()
            (papers / "Theory.lean").write_text(
                "public import Theory.Current\n",
                encoding="utf-8",
            )
            namespace = papers / "Theory"
            namespace.mkdir()
            (namespace / "Current.lean").write_text(
                "import Mathlib\n",
                encoding="utf-8",
            )
            (namespace / "Unused.lean").write_text(
                "import Mathlib\n",
                encoding="utf-8",
            )
            self._write_olean(project, "Theory")
            self._write_olean(project, "Theory.Current")
            runner = _DocsRunner()

            result = ProjectDocumentationBuilder(runner=runner).build(
                project,
                ("Theory",),
                root / "cache" / "docs-explicit",
            )

            self.assertEqual(result.targets, ("Theory",))
            self.assertEqual(runner.modules, ["Theory", "Theory.Current"])
            self.assertEqual(len(result.pages), 2)

    def test_publish_failure_restores_previous_docs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = self._project(root, modern=False)
            output = root / "cache" / "docs"
            output.mkdir(parents=True)
            (output / "sentinel.txt").write_text("previous", encoding="utf-8")
            real_replace = docs_module.os.replace
            calls = 0

            def fail_publication(source, destination):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise OSError("simulated publication failure")
                return real_replace(source, destination)

            with patch(
                "reasbook_build_sdk.docs.os.replace",
                side_effect=fail_publication,
            ):
                with self.assertRaises(OSError):
                    ProjectDocumentationBuilder(runner=_DocsRunner()).build(
                        project,
                        ("Books.Demo.Book",),
                        output,
                    )

            self.assertEqual(
                (output / "sentinel.txt").read_text(encoding="utf-8"),
                "previous",
            )
            self.assertEqual(list(output.parent.glob(".docs.backup-*")), [])


if __name__ == "__main__":
    unittest.main()
