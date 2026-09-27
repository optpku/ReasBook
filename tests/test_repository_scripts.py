from __future__ import annotations

from contextlib import contextmanager
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
PAGES = ROOT / "scripts" / "pages"
if str(PAGES) not in sys.path:
    sys.path.insert(0, str(PAGES))

import assemble  # noqa: E402
import update_readme  # noqa: E402
import verify  # noqa: E402


@contextmanager
def working_directory(path: Path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


class RepositoryScriptTests(unittest.TestCase):
    def test_missing_api_link_requires_verified_matching_pinned_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            original = "https://github.com/acme/books/blob/v4.30.0/ReasBook/Demo/Item.lean"
            pinned = original.replace("v4.30.0", "a" * 40)
            doc = root / "index.html"
            source = ('<main><p>Item (<a href="/ReasBook/docs/Item.html">API documentation</a>) '
                      f'(<a href="{original}">Lean source</a>)</p>'
                      '<a href="/ReasBook/missing.html">Unrelated</a></main>')
            doc.write_text(source)
            self.assertEqual(assemble.reconcile_documentation_links(root)["replacement_count"], 0)
            result = assemble.reconcile_documentation_links(root, verified_source_links={original: pinned})
            self.assertEqual(result["replacement_count"], 1)
            text = doc.read_text()
            self.assertIn("API documentation unavailable", text)
            self.assertIn(pinned, text)
            self.assertIn('href="/ReasBook/missing.html"', text)
            self.assertFalse((root / "docs/Item.html").exists())
            for invalid in (original, pinned.replace("Item.lean", "Other.lean")):
                doc.write_text(source)
                result = assemble.reconcile_documentation_links(root, verified_source_links={original: invalid})
                self.assertEqual(result["replacement_count"], 0)
            (root / "docs").mkdir()
            (root / "docs/Item.html").write_text("Real documentation")
            doc.write_text(source)
            self.assertEqual(assemble.reconcile_documentation_links(root, verified_source_links={original: pinned})["replacement_count"], 0)

    @staticmethod
    def _project_docs_fixture(root: Path) -> tuple[Path, Path, Path, Path]:
        repo = root / "repo"
        scripts = repo / "scripts" / "build"
        build_bin = repo / "sdk" / "build" / "bin"
        deploy_bin = repo / "sdk" / "deploy" / "bin"
        lean_root = repo / "ReasBook"
        for directory in (scripts, build_bin, deploy_bin, lean_root):
            directory.mkdir(parents=True, exist_ok=True)
        for name in ("common.sh", "project_docs.sh"):
            shutil.copy2(ROOT / "scripts" / "build" / name, scripts / name)
        (lean_root / "lakefile.lean").write_text(
            'require doc-gen4 from git "https://example.invalid/doc-gen4"\n',
            encoding="utf-8",
        )
        deploy = deploy_bin / "reasbook-deploy"
        deploy.write_text(
            "#!/usr/bin/env bash\n"
            "set -eu\n"
            'while [ "$#" -gt 0 ] && [ "$1" != -- ]; do shift; done\n'
            '[ "$#" -gt 0 ] || exit 2\n'
            "shift\n"
            'exec "$@"\n',
            encoding="utf-8",
        )
        deploy.chmod(0o755)
        return repo, scripts, lean_root, build_bin / "reasbook-build"

    @staticmethod
    def _item_style_book_fixture(
        root: Path, *, item_count: int = 193
    ) -> tuple[Path, Path, Path]:
        repo = root / "checkout"
        lean_root = repo / "ReasBook"
        web_root = repo / "ReasBookWeb"
        book_root = lean_root / "Books" / "MayLike"
        chapter_root = book_root / "Chap01"
        chapter_root.mkdir(parents=True)
        (lean_root / "Papers").mkdir()
        (web_root / "ReasBookSite").mkdir(parents=True)
        (lean_root / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\n"
            'lean_lib MayLike where\n  srcDir := "Books"\n',
            encoding="utf-8",
        )
        (book_root / "book.yml").write_text(
            "schema_version: 1\n"
            'title: "A Concise Course in Test Topology" # canonical title\n'
            "statistics:\n"
            "  title: This nested field must not win\n",
            encoding="utf-8",
        )
        (book_root / "Book.lean").write_text(
            "import MayLike.Chap01\n", encoding="utf-8"
        )
        (book_root / "Chap01.lean").write_text(
            "/-!\n"
            "# Chapter 01 -- A deliberately descriptive chapter heading that is "
            "longer than the title heuristic permits\n"
            "-/\n",
            encoding="utf-8",
        )
        kinds = ("Definition", "Lemma", "ProofStep", "Construction")
        for offset in range(item_count):
            section = offset // 30 + 1
            item_number = offset % 30 + 1
            kind = kinds[offset % len(kinds)]
            stem = f"{kind}_1_{section}_{item_number}"
            (chapter_root / f"{stem}.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
        return repo, lean_root, web_root

    def test_project_docs_honors_and_validates_release_target_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo, scripts, lean_root, build_sdk = self._project_docs_fixture(Path(temp))
            build_sdk.write_text(
                "#!/usr/bin/env bash\n"
                "set -eu\n"
                'if [ "${1:-}" = targets ]; then\n'
                '  : > "$DISCOVERY_LOG"\n'
                "  printf '%s\\n' Included.Book Excluded.Book\n"
                "  exit 0\n"
                "fi\n"
                'printf \'%s\\n\' "$@" > "$INVOCATION_LOG"\n',
                encoding="utf-8",
            )
            build_sdk.chmod(0o755)

            invocation = Path(temp) / "invocation.log"
            discovery = Path(temp) / "discovery.log"
            result = subprocess.run(
                ["bash", str(scripts / "project_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_LEAN_ROOT": str(lean_root),
                    "REASBOOK_LAKE_TARGETS": "Included.Book,Second.Paper",
                    "PROJECT_DOC_MODULES": "Excluded.Book",
                    "INVOCATION_LOG": str(invocation),
                    "DISCOVERY_LOG": str(discovery),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("2 project root(s)", result.stdout)
            self.assertFalse(discovery.exists())
            arguments = invocation.read_text(encoding="utf-8").splitlines()
            self.assertEqual(
                arguments[:4],
                [
                    "project-docs",
                    str(lean_root),
                    "Included.Book",
                    "Second.Paper",
                ],
            )
            self.assertNotIn("Excluded.Book", arguments)

            empty_result = subprocess.run(
                ["bash", str(scripts / "project_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_LEAN_ROOT": str(lean_root),
                    "REASBOOK_LAKE_TARGETS": " , ",
                    "DISCOVERY_LOG": str(discovery),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(empty_result.returncode, 2)
            self.assertIn("contains no documentation roots", empty_result.stderr)
            self.assertFalse(discovery.exists())

    def test_readme_resource_labels_describe_release_state(self) -> None:
        english = (ROOT / "README.md").read_text(encoding="utf-8")
        chinese = (ROOT / "README.zh-CN.md").read_text(encoding="utf-8")
        self.assertIn("[简体中文](README.zh-CN.md)", english)
        self.assertIn("[English](README.md)", chinese)

        excluded = {
            "kind": "books",
            "name": "ProbabilityTheory_Klenke_2020",
            "slug": "probabilitytheory_klenke_2020",
        }
        no_verso = {
            "kind": "books",
            "name": "IntegerProgramming_Conforti_2014",
            "slug": "integerprogramming_conforti_2014",
        }

        self.assertEqual(
            update_readme.resource_cell(excluded),
            "Source only (excluded from the current release profile)",
        )
        resource = update_readme.resource_cell(no_verso)
        self.assertIn("Verso not published", resource)
        self.assertNotIn("TBD", resource)
        linked_resource = update_readme.resource_cell(
            {
                "kind": "books",
                "name": "Analysis2_Tao_2022",
                "slug": "analysis2_tao_2022",
            }
        )
        self.assertEqual(linked_resource.count("&#124;"), 1)
        theorem_resource = update_readme.resource_cell(
            {
                "kind": "papers",
                "name": "TR_LALM_theory",
                "slug": "tr_lalm_theory",
            }
        )
        self.assertEqual(theorem_resource.count("&#124;"), 1)
        self.assertNotIn("theorem-maps", theorem_resource)
        self.assertEqual(
            update_readme.resource_cell(excluded, language="zh-CN"),
            "仅源代码（不包含在当前发布配置中）",
        )
        chinese_resource = update_readme.resource_cell(no_verso, language="zh-CN")
        self.assertIn("尚未发布 Verso", chinese_resource)
        self.assertNotIn("TBD", chinese_resource)

    def test_public_readmes_keep_build_details_out_of_homepage(self) -> None:
        english = (ROOT / "README.md").read_text(encoding="utf-8")
        chinese = (ROOT / "README.zh-CN.md").read_text(encoding="utf-8")
        self.assertNotIn("\n## Build\n", english)
        self.assertNotIn("\n## 构建\n", chinese)
        self.assertNotIn("SiFlow", english)
        self.assertNotIn("SiFlow", chinese)
        self.assertNotIn("rather than", english)
        self.assertNotIn("而不是", chinese)
        self.assertIn('<th scope="col">Category</th>', english)
        self.assertIn('<th scope="col">项目</th>', chinese)
        for content, category, row_count in (
            (english, "Formalization project", 2),
            (english, "Benchmark", 2),
            (english, "Autoformalization and theorem proving", 3),
            (chinese, "形式化项目", 2),
            (chinese, "基准测试", 2),
            (chinese, "自动形式化与定理证明", 3),
        ):
            self.assertIn(
                f'<td rowspan="{row_count}" scope="rowgroup">{category}</td>',
                content,
            )
        self.assertIn('<td scope="rowgroup">Formalization platform</td>', english)
        self.assertIn('<td scope="rowgroup">形式化平台</td>', chinese)
        self.assertGreater(english.count("&#124;"), 0)
        self.assertEqual(english.count("&#124;"), chinese.count("&#124;"))
        self.assertIn("https://github.com/leanprover/verso", english)
        self.assertIn("https://github.com/leanprover/comparator", english)
        self.assertIn("https://github.com/leanprover/verso", chinese)
        self.assertIn("https://github.com/leanprover/comparator", chinese)

    def test_verso_build_validates_literate_cache_before_prebuilt_mode(self) -> None:
        script = (ROOT / "scripts" / "build" / "verso.sh").read_text(encoding="utf-8")
        generated = script.index('"${generator_args[@]}"')
        cached = script.index(
            'reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$LITERATE_SDK"'
        )
        enabled = script.index("export REASBOOK_LITERATE_PREBUILT=1")
        built = script.index('reasbook_run_runtime "$REASBOOK_WEB_ROOT"')
        self.assertLess(generated, cached)
        self.assertLess(cached, enabled)
        self.assertLess(enabled, built)
        self.assertIn('export VERSO_GENERATOR=""', script)
        self.assertIn("export VERSO_ENV_REASBOOK_LITERATE_PREBUILT=1", script)

    def test_verso_literate_failure_stops_before_web_build(self) -> None:
        source_scripts = ROOT / "scripts" / "build"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "repo"
            scripts = repo / "scripts" / "build"
            for directory in (
                scripts,
                repo / "sdk/common/bin",
                repo / "sdk/deploy/bin",
                repo / "sdk/verso/bin",
                repo / "ReasBook",
                repo / "ReasBookWeb",
            ):
                directory.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_scripts / "common.sh", scripts / "common.sh")
            shutil.copy2(source_scripts / "verso.sh", scripts / "verso.sh")
            (repo / "sdk/common/bin/python").symlink_to(sys.executable)
            generator = repo / "generator.py"
            generator.write_text(
                "from pathlib import Path\n"
                "Path('ReasBookWeb/.literate-modules.json').write_text("
                '\'{"schema_version":1,"modules":["Demo"]}\\n\')\n',
                encoding="utf-8",
            )
            deploy = repo / "sdk/deploy/bin/reasbook-deploy"
            deploy.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "while [[ $# -gt 0 && $1 != -- ]]; do shift; done\n"
                "shift\n"
                "export REASBOOK_BUILD_LAKE_BIN=/runtime/lake\n"
                'exec "$@"\n',
                encoding="utf-8",
            )
            deploy.chmod(0o755)
            literate = repo / "sdk/verso/bin/verso-literate"
            literate.write_text(
                "#!/usr/bin/env bash\n"
                'test "${REASBOOK_BUILD_LAKE_BIN:-}" = /runtime/lake\n'
                "exit 17\n",
                encoding="utf-8",
            )
            literate.chmod(0o755)
            web_marker = repo / "web-build-ran"
            web = repo / "sdk/verso/bin/verso-build"
            web.write_text(
                f"#!/usr/bin/env bash\ntouch {web_marker}\n",
                encoding="utf-8",
            )
            web.chmod(0o755)

            result = subprocess.run(
                ["bash", str(scripts / "verso.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_LEAN_ROOT": str(repo / "ReasBook"),
                    "REASBOOK_WEB_ROOT": str(repo / "ReasBookWeb"),
                    "REASBOOK_VERSO_GENERATOR": str(generator),
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 17, result.stderr)
            self.assertFalse(web_marker.exists())

    def test_catalog_display_names_preserve_bibliographic_structure(self) -> None:
        self.assertEqual(
            assemble.display_name("RiemannSurfaces_Forster_1981"),
            "Riemann Surfaces (Forster, 1981)",
        )
        self.assertEqual(
            assemble.display_name("IntroductiontoRealAnalysisVolumeI_JiriLebl_2025"),
            "Introduction to Real Analysis Volume I (Jiri Lebl, 2025)",
        )
        self.assertEqual(
            assemble.display_name("TR_LALM_theory"),
            "TR-LALM Theory",
        )

    def test_gen_sections_accepts_option_repo_root(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            (lean_root / "Books" / "DemoBook").mkdir(parents=True)
            (lean_root / "Papers").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\nlean_lib Books where\n",
                encoding="utf-8",
            )
            (lean_root / "Books" / "DemoBook" / "Book.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            (lean_root / "Books" / "DemoBook" / "Chap01.lean").write_text(
                "/-!\n" "# Chapter 01 -- A Descriptive Demo Chapter Title\n" "-/\n",
                encoding="utf-8",
            )

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={**os.environ, "REASBOOK_GITHUB_BRANCH": "main"},
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((web_root / "ReasBookSite" / "Sections.lean").is_file())
            sections = (web_root / "ReasBookSite" / "Sections.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn("demobook/chap01/", sections)
            literate_manifest = json.loads(
                (web_root / ".literate-modules.json").read_text(encoding="utf-8")
            )
            self.assertEqual(literate_manifest["schema_version"], 1)
            self.assertEqual(
                (web_root / ".literate-modules.json").stat().st_mode & 0o777,
                0o644,
            )
            self.assertEqual(
                literate_manifest["modules"],
                ["Books.DemoBook.Book", "Books.DemoBook.Chap01"],
            )
            home = (web_root / "ReasBookSite" / "Home.lean").read_text(encoding="utf-8")
            self.assertIn("API documentation", home)
            self.assertNotIn("python3 scripts/gen_sections.py", home)

    def test_gen_sections_builds_compact_item_style_chapter_readers(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo, _lean_root, web_root = self._item_style_book_fixture(Path(temp))
            generated_marker = (
                "-- This item-style chapter page is generated by "
                "scripts/gen_sections.py\n"
            )
            stale = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Books"
                / "OldBook"
                / "Chap09.lean"
            )
            stale.parent.mkdir(parents=True)
            stale.write_text(generated_marker, encoding="utf-8")
            hand_written = stale.parent / "Chap10.lean"
            hand_written.write_text("-- maintained by a human\n", encoding="utf-8")

            command = [sys.executable, str(generator), "--repo-root", str(repo)]
            environment = {
                **os.environ,
                "REASBOOK_INCLUDE_PROJECTS": "",
                "REASBOOK_EXCLUDE_PROJECTS": "",
                "REASBOOK_PROJECT_FRAGMENT": "0",
                "REASBOOK_GITHUB_BRANCH": "main",
            }
            result = subprocess.run(
                command,
                cwd=repo,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("1 compact chapter reader(s) for 193", result.stdout)
            self.assertFalse(stale.exists())
            self.assertEqual(
                hand_written.read_text(encoding="utf-8"),
                "-- maintained by a human\n",
            )

            literate_path = web_root / ".literate-modules.json"
            literate = json.loads(literate_path.read_text(encoding="utf-8"))
            self.assertEqual(literate["modules"], ["MayLike.Book", "MayLike.Chap01"])
            self.assertFalse(
                any("Definition_" in module for module in literate["modules"])
            )
            self.assertFalse(
                any("ProofStep_" in module for module in literate["modules"])
            )

            sections_path = web_root / "ReasBookSite" / "Sections.lean"
            sections = sections_path.read_text(encoding="utf-8")
            self.assertIn("A Concise Course in Test Topology", sections)
            self.assertIn(r"\"route\":\"books/maylike/chapters/chap01/\"", sections)

            home_page = (
                web_root / "ReasBookSite" / "WorkPages" / "Books" / "MayLike.lean"
            )
            home = home_page.read_text(encoding="utf-8")
            self.assertIn('#doc (Page) "A Concise Course in Test Topology"', home)
            self.assertIn("Chapter index:", home)
            self.assertIn("7 sections, 193 items", home)

            chapter_page = home_page.parent / "MayLike" / "Chap01.lean"
            chapter = chapter_page.read_text(encoding="utf-8")
            self.assertTrue(chapter.startswith(generated_marker.rstrip("\n")))
            self.assertIn("# Section 1.1", chapter)
            self.assertIn("# Section 1.7", chapter)
            self.assertNotIn("## Section", chapter)
            self.assertEqual(chapter.count("([API documentation]"), 193)
            self.assertIn(
                "/ReasBook/docs/ReasBook/MayLike/Chap01/Definition_1_1_1.html",
                chapter,
            )
            self.assertIn(
                "/blob/main/ReasBook/Books/MayLike/Chap01/Definition_1_1_1.lean",
                chapter,
            )

            route_path = web_root / "ReasBookSite" / "RouteTable.lean"
            route_table = route_path.read_text(encoding="utf-8")
            macro_block = route_table.split("def reasbook_site", maxsplit=1)[0]
            routes = re.findall(
                r'^\s{6}"([^"]+/)"\s+\S+', macro_block, flags=re.MULTILINE
            )
            self.assertEqual(len(routes), len(set(routes)))
            self.assertEqual(routes.count("books/maylike/chapters/chap01/"), 1)
            self.assertEqual(routes.count("maylike/chap01/"), 1)
            self.assertIn(
                '"books/maylike/chapters/chap01/" '
                "ReasBookSite.WorkPages.Books.MayLike.Chap01",
                macro_block,
            )

            watched = (
                literate_path,
                sections_path,
                route_path,
                home_page,
                chapter_page,
            )
            snapshot = {
                path: (path.read_bytes(), path.stat().st_mtime_ns) for path in watched
            }
            second = subprocess.run(
                command,
                cwd=repo,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(
                snapshot,
                {
                    path: (path.read_bytes(), path.stat().st_mtime_ns)
                    for path in watched
                },
            )

    def test_gen_sections_item_style_fragment_owns_reader_routes(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo, lean_root, web_root = self._item_style_book_fixture(
                Path(temp), item_count=5
            )
            book_source = lean_root / "Books" / "MayLike" / "Book.lean"
            chapter_source = lean_root / "Books" / "MayLike" / "Chap01.lean"
            original_chapter_dir = chapter_source.with_suffix("")
            actual_chapter_dir = chapter_source.parent / "Parts" / "Chap01"
            actual_chapter_dir.parent.mkdir()
            original_chapter_dir.rename(actual_chapter_dir)
            # A fragment can still own a synthetic reader when the item
            # directory has no matching aggregation module.
            book_source.write_text("import Mathlib\n", encoding="utf-8")
            chapter_source.unlink()
            original_book_source = book_source.read_bytes()
            root_readme = repo / "README.md"
            root_readme.write_text("catalog sentinel\n", encoding="utf-8")
            marker = (
                "-- This item-style chapter page is generated by "
                "scripts/gen_sections.py\n"
            )
            selected_stale = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Books"
                / "MayLike"
                / "Chap09.lean"
            )
            unrelated_stale = selected_stale.parents[1] / "OtherBook" / "Chap09.lean"
            selected_stale.parent.mkdir(parents=True)
            unrelated_stale.parent.mkdir(parents=True)
            selected_stale.write_text(marker, encoding="utf-8")
            unrelated_stale.write_text(marker, encoding="utf-8")

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/MayLike",
                    "REASBOOK_EXCLUDE_PROJECTS": "",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(original_book_source, book_source.read_bytes())
            self.assertFalse(chapter_source.exists())
            self.assertFalse(selected_stale.exists())
            self.assertTrue(unrelated_stale.exists())
            self.assertEqual(
                root_readme.read_text(encoding="utf-8"), "catalog sentinel\n"
            )

            fragment = json.loads(
                (web_root / ".project-fragment.json").read_text(encoding="utf-8")
            )
            self.assertEqual(fragment["project"], "books/MayLike")
            self.assertEqual(fragment["modules"], ["MayLike.Book"])
            self.assertIn("books/maylike/chapters/chap01/", fragment["routes"])
            self.assertNotIn("maylike/chap01/", fragment["routes"])
            self.assertEqual(len(fragment["routes"]), len(set(fragment["routes"])))

            sections = (web_root / "ReasBookSite" / "Sections.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn(r"\"route\":\"books/maylike/chapters/chap01/\"", sections)
            chapter_page = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Books"
                / "MayLike"
                / "Chap01.lean"
            ).read_text(encoding="utf-8")
            self.assertEqual(chapter_page.count("([API documentation]"), 5)
            self.assertIn("/ReasBook/Books/MayLike/Parts/Chap01", chapter_page)

    def test_gen_sections_classifies_mixed_item_inventory_without_partial_takeover(
        self,
    ) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            book_root = lean_root / "Books" / "BauschkeLike"
            chapter_one = book_root / "Chap01"
            chapter_two = book_root / "Chap02"
            chapter_one.mkdir(parents=True)
            chapter_two.mkdir()
            (lean_root / "Papers").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                'lean_lib BauschkeLike where\n  srcDir := "Books"\n',
                encoding="utf-8",
            )
            (book_root / "Book.lean").write_text("import Mathlib\n", encoding="utf-8")
            for chapter in (1, 2):
                (book_root / f"Chap{chapter:02d}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )

            item_stems = (
                "Definition_1_1",
                "Definition_1_1_1",
                "Text_1_0_1",
                "Definition_1_2_extra_1",
                "Theorem_1_2_2",
                "Lemma_1_3_1",
                "Example_1_4_1",
            )
            for stem in item_stems:
                (chapter_one / f"{stem}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
            (chapter_one / "Section_1_2_introduction.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            for stem in ("Helper_1_1", "Lemma_9_1"):
                (chapter_one / f"{stem}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
            nested_support = chapter_one / "Definition_1_1" / "Implementation.lean"
            nested_support.parent.mkdir()
            nested_support.write_text("import Mathlib\n", encoding="utf-8")

            # This chapter is section-dominant. Its one item-shaped module
            # stays a literate target instead of triggering a partial reader.
            (chapter_two / "Definition_2_1.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            for section in (1, 2):
                (chapter_two / f"Section_2_{section}_introduction.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_INCLUDE_PROJECTS": "books/BauschkeLike",
                    "REASBOOK_EXCLUDE_PROJECTS": "",
                    "REASBOOK_PROJECT_FRAGMENT": "0",
                    "REASBOOK_GITHUB_REPO": "example/reasbook-test",
                    "REASBOOK_GITHUB_BRANCH": "test-branch",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            literate = json.loads(
                (web_root / ".literate-modules.json").read_text(encoding="utf-8")
            )["modules"]
            self.assertIn("BauschkeLike.Chap02.Definition_2_1", literate)
            for stem in item_stems:
                self.assertNotIn(f"BauschkeLike.Chap01.{stem}", literate)

            home = (
                web_root / "ReasBookSite" / "WorkPages" / "Books" / "BauschkeLike.lean"
            ).read_text(encoding="utf-8")
            self.assertIn("Chapter index:", home)
            self.assertIn("Section index:", home)
            self.assertEqual(home.count("books/bauschkelike/chapters/chap01/"), 1)

            reader = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Books"
                / "BauschkeLike"
                / "Chap01.lean"
            ).read_text(encoding="utf-8")
            self.assertIn("indexes 7 formalized items and 3 supporting", reader)
            self.assertIn("# Reading sections", reader)
            self.assertIn("# Chapter items", reader)
            self.assertIn("# Section 1.2", reader)
            self.assertIn("Definition 1.2.extra.1", reader)
            self.assertIn("`Helper_1_1.lean`", reader)
            self.assertIn("`Lemma_9_1.lean`", reader)
            self.assertIn("`Definition_1_1/Implementation.lean`", reader)
            self.assertIn(
                "https://github.com/example/reasbook-test/blob/test-branch/"
                "ReasBook/Books/BauschkeLike/Chap01/Helper_1_1.lean",
                reader,
            )
            self.assertIn(
                "https://github.com/example/reasbook-test/blob/test-branch/"
                "ReasBook/Books/BauschkeLike/Chap01/Definition_1_1/"
                "Implementation.lean",
                reader,
            )
            self.assertNotIn("## ", reader)
            self.assertFalse(
                (
                    web_root
                    / "ReasBookSite"
                    / "WorkPages"
                    / "Books"
                    / "BauschkeLike"
                    / "Chap02.lean"
                ).exists()
            )

            sections = (web_root / "ReasBookSite" / "Sections.lean").read_text(
                encoding="utf-8"
            )
            self.assertNotIn("Definition_1_2_extra_1", sections)
            self.assertIn(r"\"number\":2", sections)

    def test_gen_sections_refuses_unowned_reader_work_page(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo, _lean_root, web_root = self._item_style_book_fixture(
                Path(temp), item_count=5
            )
            target = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Books"
                / "MayLike"
                / "Chap01.lean"
            )
            target.parent.mkdir(parents=True)
            target.write_text("-- hand maintained\n", encoding="utf-8")

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_INCLUDE_PROJECTS": "books/MayLike",
                    "REASBOOK_EXCLUDE_PROJECTS": "",
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("refusing to overwrite non-generated", result.stderr)
            self.assertEqual(target.read_text(encoding="utf-8"), "-- hand maintained\n")

    def test_gen_sections_builds_compact_item_style_paper_reader(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            paper_root = lean_root / "Papers" / "TR_LALM_theory"
            paper_root.mkdir(parents=True)
            (lean_root / "Books").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                "lean_lib TR_LALM_theory where\n"
                '  srcDir := "Papers"\n'
                "  roots := #[`TR_LALM_theory]\n",
                encoding="utf-8",
            )
            (lean_root / "Papers" / "TR_LALM_theory.lean").write_text(
                "import TR_LALM_theory.Paper\n", encoding="utf-8"
            )
            (paper_root / "Paper.lean").write_text(
                "import TR_LALM_theory.Theorem_2_9\n", encoding="utf-8"
            )
            item_stems = (
                "Algorithm_2_1",
                "Theorem_2_9",
                "Corollary_3_8",
                "Remark_C_1",
            )
            for stem in item_stems:
                (paper_root / f"{stem}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
            nested = paper_root / "Theorem_2_9" / "OperationalTrace.lean"
            nested.parent.mkdir()
            nested.write_text("import Mathlib\n", encoding="utf-8")
            (paper_root / "Current.lean").write_text(
                "import TR_LALM_theory.Theorem_2_9\n", encoding="utf-8"
            )

            unrelated_reader = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Papers"
                / "Unrelated"
                / "Items.lean"
            )
            unrelated_reader.parent.mkdir(parents=True)
            unrelated_reader.write_text(
                "-- This item-style paper page is generated by "
                "scripts/gen_sections.py\n",
                encoding="utf-8",
            )
            env = {
                **os.environ,
                "REASBOOK_PROJECT_FRAGMENT": "1",
                "REASBOOK_INCLUDE_PROJECTS": "papers/TR_LALM_theory",
                "REASBOOK_EXCLUDE_PROJECTS": "",
            }
            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            manifest = json.loads(
                (web_root / ".literate-modules.json").read_text(encoding="utf-8")
            )["modules"]
            self.assertEqual(manifest, ["TR_LALM_theory.Paper"])
            for stem in item_stems:
                self.assertFalse(any(stem in module for module in manifest))

            home_path = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Papers"
                / "TR_LALM_theory.lean"
            )
            reader_path = home_path.with_suffix("") / "Items.lean"
            home = home_path.read_text(encoding="utf-8")
            reader = reader_path.read_text(encoding="utf-8")
            self.assertIn("TR-LALM Theory", home)
            self.assertIn("papers/tr_lalm_theory/items/", home)
            self.assertIn("indexes 4 formalized items", reader)
            self.assertIn("# Section 2", reader)
            self.assertIn("# Section 3", reader)
            self.assertIn("# Appendix C", reader)
            self.assertIn("Theorem 2.9", reader)
            self.assertIn("Remark C.1", reader)
            self.assertEqual(reader.count("[API documentation]"), 4)
            self.assertEqual(reader.count("[Lean source]"), 4)
            self.assertNotIn("OperationalTrace", reader)
            self.assertNotIn("## ", reader)

            sections = (web_root / "ReasBookSite" / "Sections.lean").read_text(
                encoding="utf-8"
            )
            self.assertNotIn("Theorem_2_9", sections)
            self.assertNotIn("Remark_C_1", sections)
            fragment = json.loads(
                (web_root / ".project-fragment.json").read_text(encoding="utf-8")
            )
            self.assertIn("papers/tr_lalm_theory/items/", fragment["routes"])
            self.assertEqual(len(fragment["routes"]), len(set(fragment["routes"])))
            self.assertIn(
                '"papers/tr_lalm_theory/items/" '
                "ReasBookSite.WorkPages.Papers.TR_LALM_theory.Items",
                (web_root / "ReasBookSite" / "RouteTable.lean").read_text(
                    encoding="utf-8"
                ),
            )

            before = (reader_path.read_bytes(), reader_path.stat().st_mtime_ns)
            repeat = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(repeat.returncode, 0, repeat.stderr)
            self.assertEqual(
                before, (reader_path.read_bytes(), reader_path.stat().st_mtime_ns)
            )
            self.assertTrue(unrelated_reader.exists())

    def test_gen_sections_indexes_imports_only_paper_sections_with_parts(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            paper_root = lean_root / "Papers" / "PartedPaper"
            paper_root.mkdir(parents=True)
            (lean_root / "Books").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                'lean_lib PartedPaper where\n  srcDir := "Papers"\n',
                encoding="utf-8",
            )
            (paper_root / "Paper.lean").write_text(
                "import PartedPaper.section01\n", encoding="utf-8"
            )
            (paper_root / "section01.lean").write_text(
                "/-! Generated-looking prose is still only a comment. -/\n"
                "import Mathlib\n"
                "import PartedPaper.section01_part1\n"
                "import PartedPaper.section01_part2 -- second part\n",
                encoding="utf-8",
            )
            for part in (1, 2):
                (paper_root / f"section01_part{part}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
            (paper_root / "section02.lean").write_text(
                "import PartedPaper.section02_part1\n\n"
                "def substantiveParent : Nat := 1\n",
                encoding="utf-8",
            )
            (paper_root / "section02_part1.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )

            selected_stale = (
                web_root
                / "ReasBookSite"
                / "WorkPages"
                / "Papers"
                / "PartedPaper"
                / "Section09.lean"
            )
            unrelated_stale = selected_stale.parents[1] / "Other" / "Section09.lean"
            for path in (selected_stale, unrelated_stale):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    "-- This paper section index is generated by "
                    "scripts/gen_sections.py\n",
                    encoding="utf-8",
                )

            env = {
                **os.environ,
                "REASBOOK_PROJECT_FRAGMENT": "1",
                "REASBOOK_INCLUDE_PROJECTS": "papers/PartedPaper",
                "REASBOOK_EXCLUDE_PROJECTS": "",
            }
            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            section_dir = (
                web_root / "ReasBookSite" / "WorkPages" / "Papers" / "PartedPaper"
            )
            section_one_path = section_dir / "Section01.lean"
            self.assertTrue(section_one_path.is_file())
            self.assertFalse((section_dir / "Section02.lean").exists())
            self.assertFalse(selected_stale.exists())
            self.assertTrue(unrelated_stale.exists())
            page = section_one_path.read_text(encoding="utf-8")
            self.assertIn("[Parent API documentation]", page)
            self.assertIn("[Parent Lean source]", page)
            self.assertIn("# Parts", page)
            self.assertEqual(page.count("[Reading page]"), 2)
            self.assertEqual(page.count("[API documentation]"), 2)
            self.assertEqual(page.count("[Lean source]"), 2)
            self.assertNotIn("## ", page)

            routes = (web_root / "ReasBookSite" / "RouteTable.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn(
                '"partedpaper/section01/" '
                "ReasBookSite.WorkPages.Papers.PartedPaper.Section01",
                routes,
            )
            self.assertIn('"partedpaper/section02/" Book.PartedPaper.section02', routes)
            fragment = json.loads(
                (web_root / ".project-fragment.json").read_text(encoding="utf-8")
            )
            for route in (
                "partedpaper/section01/",
                "partedpaper/section01_part1/",
                "partedpaper/section01_part2/",
            ):
                self.assertIn(route, fragment["routes"])
            self.assertEqual(len(fragment["routes"]), len(set(fragment["routes"])))

            section_one_path.write_text("-- hand maintained\n", encoding="utf-8")
            refused = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn(
                "refusing to overwrite non-generated paper section", refused.stderr
            )
            self.assertEqual(
                section_one_path.read_text(encoding="utf-8"), "-- hand maintained\n"
            )

    def test_gen_sections_requires_parent_to_import_every_paper_part(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            paper_root = lean_root / "Papers" / "IncompleteImports"
            paper_root.mkdir(parents=True)
            (lean_root / "Books").mkdir()
            (web_root / "ReasBookSite").mkdir(parents=True)
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                'lean_lib IncompleteImports where\n  srcDir := "Papers"\n',
                encoding="utf-8",
            )
            (paper_root / "Paper.lean").write_text(
                "import IncompleteImports.section01\n", encoding="utf-8"
            )

            # A same-stem import from another namespace is not ownership of
            # the locally discovered part module.
            (paper_root / "section01.lean").write_text(
                "import Other.section01_part1\n", encoding="utf-8"
            )
            (paper_root / "section01_part1.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )

            # Importing only a subset of the discovered parts must likewise
            # retain the original literate parent route.
            (paper_root / "section02.lean").write_text(
                "import Mathlib\n" "import IncompleteImports.section02_part1\n",
                encoding="utf-8",
            )
            for part in (1, 2):
                (paper_root / f"section02_part{part}.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "papers/IncompleteImports",
                    "REASBOOK_EXCLUDE_PROJECTS": "",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            generated_dir = (
                web_root / "ReasBookSite" / "WorkPages" / "Papers" / "IncompleteImports"
            )
            self.assertFalse((generated_dir / "Section01.lean").exists())
            self.assertFalse((generated_dir / "Section02.lean").exists())
            routes = (web_root / "ReasBookSite" / "RouteTable.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn(
                '"incompleteimports/section01/" ' "Book.IncompleteImports.section01",
                routes,
            )
            self.assertIn(
                '"incompleteimports/section02/" ' "Book.IncompleteImports.section02",
                routes,
            )
            manifest = json.loads(
                (web_root / ".literate-modules.json").read_text(encoding="utf-8")
            )["modules"]
            self.assertIn("IncompleteImports.section01_part1", manifest)
            self.assertIn("IncompleteImports.section02_part1", manifest)
            self.assertIn("IncompleteImports.section02_part2", manifest)

    def test_gen_sections_links_project_docs_by_lake_root(self) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        layouts = {
            "aggregate": (
                "lean_lib Papers where\n",
                "Papers/DemoTheory/Paper.html",
            ),
            "flat": (
                'lean_lib DemoTheory where\n  srcDir := "Papers"\n',
                "DemoTheory/Paper.html",
            ),
            "explicit-root": (
                "lean_lib DemoTheory where\n"
                '  srcDir := "Papers"\n'
                "  roots := #[`DemoTheory]\n",
                "DemoTheory.html",
            ),
        }
        for name, (declaration, docs_path) in layouts.items():
            with self.subTest(layout=name), tempfile.TemporaryDirectory() as temp:
                repo = Path(temp) / "checkout"
                lean_root = repo / "ReasBook"
                paper_root = lean_root / "Papers" / "DemoTheory"
                web_root = repo / "ReasBookWeb"
                paper_root.mkdir(parents=True)
                (web_root / "ReasBookSite").mkdir(parents=True)
                (lean_root / "Books").mkdir()
                (lean_root / "lakefile.lean").write_text(
                    "import Lake\nopen Lake DSL\n" + declaration,
                    encoding="utf-8",
                )
                (paper_root / "Paper.lean").write_text(
                    "import Mathlib\n",
                    encoding="utf-8",
                )
                if name == "explicit-root":
                    (lean_root / "Papers" / "DemoTheory.lean").write_text(
                        "import DemoTheory.Paper\n",
                        encoding="utf-8",
                    )

                result = subprocess.run(
                    [sys.executable, str(generator), "--repo-root", str(repo)],
                    cwd=repo,
                    env={
                        **os.environ,
                        "REASBOOK_INCLUDE_PROJECTS": "papers/DemoTheory",
                    },
                    capture_output=True,
                    text=True,
                    check=False,
                )

                self.assertEqual(result.returncode, 0, result.stderr)
                page = (
                    web_root
                    / "ReasBookSite"
                    / "WorkPages"
                    / "Papers"
                    / "DemoTheory.lean"
                ).read_text(encoding="utf-8")
                self.assertIn(f"docs/ReasBook/{docs_path}", page)

    def test_gen_sections_project_fragment_is_exact_and_does_not_rewrite_catalog_docs(
        self,
    ) -> None:
        generator = ROOT / "ReasBookWeb" / "scripts" / "gen_sections.py"
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            lean_root = repo / "ReasBook"
            web_root = repo / "ReasBookWeb"
            for name in ("Selected", "Unselected"):
                project = lean_root / "Books" / name
                project.mkdir(parents=True)
                (project / "Book.lean").write_text("import Mathlib\n", encoding="utf-8")
            (lean_root / "Papers").mkdir()
            (lean_root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n"
                'lean_lib Selected where\n  srcDir := "Books"\n'
                'lean_lib Unselected where\n  srcDir := "Books"\n',
                encoding="utf-8",
            )
            (web_root / "ReasBookSite").mkdir(parents=True)
            root_readme = repo / "README.md"
            root_readme.write_text("branch catalog sentinel\n", encoding="utf-8")

            result = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/Selected",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            sections = (web_root / "ReasBookSite" / "Sections.lean").read_text(
                encoding="utf-8"
            )
            self.assertIn("Selected.Book", sections)
            self.assertNotIn("Unselected.Book", sections)
            self.assertEqual(
                root_readme.read_text(encoding="utf-8"), "branch catalog sentinel\n"
            )

            invalid = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/Missing",
                },
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(invalid.returncode, 0)
            self.assertIn("does not exist", invalid.stderr)

            multiple = subprocess.run(
                [sys.executable, str(generator), "--repo-root", str(repo)],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/Selected,books/Unselected",
                },
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(multiple.returncode, 0)
            self.assertIn("requires exactly one", multiple.stderr)

    def test_verso_project_fragment_requires_isolated_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            scripts = repo / "scripts" / "build"
            scripts.mkdir(parents=True)
            shutil.copy2(
                ROOT / "scripts" / "build" / "common.sh", scripts / "common.sh"
            )
            shutil.copy2(ROOT / "scripts" / "build" / "verso.sh", scripts / "verso.sh")
            for name in ("verso-build", "verso-literate"):
                executable = repo / "sdk" / "verso" / "bin" / name
                executable.parent.mkdir(parents=True, exist_ok=True)
                executable.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
                executable.chmod(0o755)
            (repo / "sdk" / "common" / "bin").mkdir(parents=True)
            (repo / "ReasBookWeb").mkdir()
            (repo / "ReasBook").mkdir()

            result = subprocess.run(
                ["bash", str(scripts / "verso.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/Selected",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("REASBOOK_PROJECT_FRAGMENT_ROOT is required", result.stderr)

    def test_verso_project_fragment_writes_validated_disjoint_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            scripts = repo / "scripts" / "build"
            scripts.mkdir(parents=True)
            for name in ("common.sh", "verso.sh"):
                shutil.copy2(ROOT / "scripts" / "build" / name, scripts / name)
            web = repo / "ReasBookWeb"
            lean = repo / "ReasBook"
            web.mkdir()
            lean.mkdir()

            common_python = repo / "sdk" / "common" / "bin" / "python"
            common_python.parent.mkdir(parents=True)
            common_python.write_text(
                f'#!/usr/bin/env bash\nexec {sys.executable!s} "$@"\n',
                encoding="utf-8",
            )
            common_python.chmod(0o755)
            deploy = repo / "sdk" / "deploy" / "bin" / "reasbook-deploy"
            deploy.parent.mkdir(parents=True)
            deploy.write_text(
                "#!/usr/bin/env bash\nset -eu\n"
                'while [ "$1" != -- ]; do shift; done\nshift\nexec "$@"\n',
                encoding="utf-8",
            )
            deploy.chmod(0o755)
            verso_bin = repo / "sdk" / "verso" / "bin"
            verso_bin.mkdir(parents=True)
            literate = verso_bin / "verso-literate"
            literate.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
            literate.chmod(0o755)
            build = verso_bin / "verso-build"
            build.write_text(
                "#!/usr/bin/env bash\nset -eu\n"
                'exec "$REASBOOK_TEST_PYTHON" -m verso_build_sdk "$@"\n',
                encoding="utf-8",
            )
            build.chmod(0o755)
            executable_argv = Path(temp) / "verso-executable-argv"
            fake_elan = repo / "fake-elan"
            fake_elan.write_text(
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf \'%s\\n\' "$@" > "$VERSO_EXECUTABLE_ARGV"\n'
                'output=""\n'
                'while [[ "$#" -gt 0 ]]; do\n'
                '  if [[ "$1" == --output ]]; then\n'
                '    [[ "$#" -ge 2 ]] || exit 9\n'
                '    output="$2"\n'
                "    shift 2\n"
                "  else\n"
                "    shift\n"
                "  fi\n"
                "done\n"
                '[[ -n "$output" && "$output" == /* ]] || exit 8\n'
                'mkdir -p "$output/books/selected/book"\n'
                ': > "$output/index.html"\n'
                ': > "$output/books/selected/index.html"\n'
                ': > "$output/books/selected/book/index.html"\n',
                encoding="utf-8",
            )
            fake_elan.chmod(0o755)
            (web / "lakefile.lean").write_text(
                'import Lake\npackage "demo-site" where\n', encoding="utf-8"
            )
            (web / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            generator = repo / "generator.py"
            generator.write_text(
                "import json, os\nfrom pathlib import Path\n"
                'web = Path(os.environ["REASBOOK_WEB_ROOT"])\n'
                '(web / ".literate-modules.json").write_text("{}\\n")\n'
                '(web / ".project-fragment.json").write_text(json.dumps({'
                '"schema_version": 1, "project": "books/Selected", '
                '"modules": ["Books.Selected.Book"], '
                '"routes": ["books/selected/", "books/selected/book/"], '
                '"shared_catalog": False}))\n',
                encoding="utf-8",
            )
            fragments = Path(temp) / "fragments"
            pythonpath = os.pathsep.join(
                (
                    str(ROOT / "sdk" / "common" / "src"),
                    str(ROOT / "sdk" / "verso" / "src"),
                )
            )

            result = subprocess.run(
                ["bash", str(scripts / "verso.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_PROJECT_FRAGMENT": "1",
                    "REASBOOK_INCLUDE_PROJECTS": "books/Selected",
                    "REASBOOK_PROJECT_FRAGMENT_ROOT": str(fragments),
                    "REASBOOK_VERSO_GENERATOR": str(generator),
                    "REASBOOK_TEST_PYTHON": sys.executable,
                    "VERSO_ELAN_BIN": str(fake_elan),
                    "VERSO_EXECUTABLE_ARGV": str(executable_argv),
                    "PYTHONPATH": pythonpath,
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            root = fragments / "books" / "Selected"
            payload = json.loads((root / "fragment.json").read_text(encoding="utf-8"))
            self.assertEqual(payload["project"], "books/Selected")
            self.assertFalse(payload["shared_catalog"])
            self.assertEqual(payload["site_dir"], "site")
            self.assertFalse((root / "site" / "index.html").exists())
            self.assertTrue(
                (root / "site" / "books" / "selected" / "index.html").is_file()
            )
            arguments = executable_argv.read_text(encoding="utf-8").splitlines()
            self.assertEqual(arguments.count("--output"), 1)
            output_option = arguments.index("--output")
            self.assertEqual(arguments[output_option + 1], str(root / "site"))
            self.assertFalse((web / "_site").exists())

    def test_pages_assembly_normalizes_docs_and_generates_landing_page(self) -> None:
        project = {
            "kind": "books",
            "kindTitle": "Books",
            "name": "DemoBook",
            "slug": "demobook",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            docs = monolith / "docs" / "ReasBook" / "Books" / "DemoBook"
            version_docs = (
                monolith / "versions" / "v4.30.0" / "docs" / "ReasBook" / "DemoBook"
            )
            chapter = monolith / "books" / "demobook" / "chapter-1"
            docs.mkdir(parents=True)
            version_docs.mkdir(parents=True)
            chapter.mkdir(parents=True)
            (monolith / "versions" / "index.html").write_text(
                "versions",
                encoding="utf-8",
            )
            (docs / "Book.html").write_text("docs", encoding="utf-8")
            (version_docs / "Book.html").write_text("versioned docs", encoding="utf-8")
            (chapter / "index.html").write_text("chapter", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()
                verify.main()

            site = root / ".site"
            self.assertTrue(
                (site / "sites" / "demobook" / "docs" / "Book.html").is_file()
            )
            self.assertTrue(
                (site / "sites" / "demobook" / "pages" / "index.html").is_file()
            )
            self.assertTrue((site / "docs" / "ReasBook" / "index.html").is_file())
            docs_index = (site / "docs" / "ReasBook" / "index.html").read_text(
                encoding="utf-8"
            )
            self.assertIn("https://github.com/optpku/ReasBook#readme", docs_index)
            self.assertNotIn("./Books/DemoBook/", docs_index)
            self.assertTrue((site / "static" / "catalog.css").is_file())
            root_page = (site / "index.html").read_text(encoding="utf-8")
            self.assertIn('id="main-content"', root_page)
            self.assertIn('http-equiv="refresh"', root_page)
            self.assertIn("https://github.com/optpku/ReasBook#readme", root_page)
            self.assertNotIn("Version Archive", root_page)
            canonical_doc = (
                site / "docs" / "ReasBook" / "Books" / "DemoBook" / "Book.html"
            ).read_text(encoding="utf-8")
            self.assertIn(
                "versions/v4.30.0/docs/ReasBook/DemoBook/Book.html",
                canonical_doc,
            )
            self.assertNotIn(".artifacts", canonical_doc)

    def test_pages_verifier_rejects_broken_internal_navigation_link(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / ".site"
            (site / "docs" / "ReasBook" / "Books").mkdir(parents=True)
            (site / "docs" / "ReasBook" / "Papers").mkdir()
            (site / "index.html").write_text(
                "<!doctype html><html><body>Home</body></html>",
                encoding="utf-8",
            )
            redirect = site / "sites" / "demo" / "docs" / "Paper.html"
            redirect.parent.mkdir(parents=True)
            redirect.write_text(
                '<meta http-equiv="refresh" content="0; url=/ReasBook/missing/">'
                '<a href="/ReasBook/">Home</a>',
                encoding="utf-8",
            )

            values = {
                "PROJECTS_JSON": "[]",
                "REASBOOK_SITE_ROOT": "/ReasBook/",
            }
            output = io.StringIO()
            with (
                working_directory(root),
                patch.dict(os.environ, values, clear=False),
                redirect_stdout(output),
                self.assertRaises(SystemExit) as raised,
            ):
                verify.main()

            self.assertEqual(raised.exception.code, 1)
            self.assertIn("Broken ReasBook links", output.getvalue())

    def test_pages_assembly_materializes_versioned_navbar_routes(self) -> None:
        project = {
            "kind": "books",
            "kindTitle": "Books",
            "name": "DemoBook",
            "slug": "demobook",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            version = monolith / "versions" / "v4.30.0"
            raw = version / "demobook"
            landing = version / "books" / "demobook"
            chapter = raw / "chap01"
            section = chapter / "section01"
            docs = version / "docs" / "ReasBook" / "DemoBook"
            for directory in (landing, section, docs):
                directory.mkdir(parents=True)
            (monolith / "versions" / "index.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            (landing / "index.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            (section / "index.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            (docs / "Book.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            alias = (
                root
                / ".site"
                / "versions"
                / "v4.30.0"
                / "books"
                / "demobook"
                / "chapters"
                / "chap01"
                / "section01"
                / "index.html"
            )
            self.assertTrue(alias.is_file())
            self.assertIn("demobook/chap01/section01/", alias.read_text())

    def test_pages_assembly_marks_only_unpublished_api_links_unavailable(self) -> None:
        project = {
            "kind": "books",
            "kindTitle": "Books",
            "name": "DemoBook",
            "slug": "demobook",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            version = monolith / "versions" / "v4.30.0"
            chapter = version / "demobook" / "chap01"
            available = chapter / "available"
            unavailable = chapter / "unavailable"
            docs = version / "docs" / "ReasBook" / "DemoBook"
            available_doc = docs / "Chap01" / "Available.html"
            for directory in (available, unavailable, available_doc.parent):
                directory.mkdir(parents=True)
            (monolith / "versions" / "index.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            (docs / "Book.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            available_doc.write_text("<!doctype html><html></html>", encoding="utf-8")
            for path in (available, unavailable):
                (path / "index.html").write_text(
                    "<!doctype html><html></html>", encoding="utf-8"
                )

            site_prefix = "/ReasBook/versions/v4.30.0/"
            (chapter / "index.html").write_text(
                "<!doctype html><html><body>"
                f'(<a href="{site_prefix}docs/ReasBook/DemoBook/Chap01/'
                'Available.html">Documentation</a>) '
                f'(<a href="{site_prefix}demobook/chap01/available/">Verso</a>) '
                f'(<a href="{site_prefix}docs/ReasBook/DemoBook/Chap01/'
                'Unavailable.html">Documentation</a>) '
                f'(<a href="{site_prefix}demobook/chap01/unavailable/">Verso</a>)'
                "</body></html>",
                encoding="utf-8",
            )

            values = {
                "PROJECTS_JSON": json.dumps([project]),
                "REASBOOK_REQUIRE_THEOREM_MAPS": "0",
                "REASBOOK_SITE_ROOT": "/ReasBook/",
            }
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()
                self.assertEqual(
                    verify._missing_internal_references(root / ".site"), []
                )

            rendered = (
                root
                / ".site"
                / "versions"
                / "v4.30.0"
                / "demobook"
                / "chap01"
                / "index.html"
            ).read_text(encoding="utf-8")
            self.assertIn('Available.html">Documentation</a>', rendered)
            self.assertNotIn('Unavailable.html">Documentation</a>', rendered)
            self.assertIn("Documentation unavailable", rendered)

            audit = json.loads(
                (root / ".site" / "unavailable-documentation.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(audit["schema_version"], 1)
            self.assertEqual(len(audit["entries"]), 1)
            self.assertGreaterEqual(audit["replacement_count"], 1)
            self.assertTrue(
                audit["entries"][0]["documentation_href"].endswith("/Unavailable.html")
            )

    def test_pages_verifier_accepts_single_page_verso_project(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoPaper",
            "slug": "demopaper",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / ".site"
            pages = site / "sites" / "demopaper" / "pages"
            project_docs = site / "sites" / "demopaper" / "docs"
            canonical_docs = site / "docs" / "ReasBook" / "Papers" / "DemoPaper"
            (site / "docs" / "ReasBook" / "Books").mkdir(parents=True)
            pages.mkdir(parents=True)
            project_docs.mkdir(parents=True)
            canonical_docs.mkdir(parents=True)
            page = "<!doctype html><html><body>Complete paper</body></html>"
            (site / "index.html").write_text(page, encoding="utf-8")
            (pages / "index.html").write_text(page, encoding="utf-8")
            (project_docs / "Paper.html").write_text(page, encoding="utf-8")
            (canonical_docs / "Paper.html").write_text(page, encoding="utf-8")

            output = io.StringIO()
            values = {
                "PROJECTS_JSON": json.dumps([project]),
                "REASBOOK_REQUIRE_DOCS": "1",
                "REASBOOK_REQUIRE_THEOREM_MAPS": "0",
                "REASBOOK_SITE_ROOT": "/ReasBook/",
            }
            with (
                working_directory(root),
                patch.dict(os.environ, values, clear=False),
                redirect_stdout(output),
            ):
                verify.main()

            self.assertIn("ReasBook pages verified", output.getvalue())

    def test_link_checker_uses_base_without_treating_it_as_navigation(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            page = site / "papers" / "demo" / "index.html"
            target = site / "docs" / "index.html"
            page.parent.mkdir(parents=True)
            target.parent.mkdir(parents=True)
            target.write_text(
                "<!doctype html><html><body>Docs</body></html>",
                encoding="utf-8",
            )
            page.write_text(
                '<!doctype html><html><head><base href="/ReasBook/">'
                '</head><body><a href="docs/">Docs</a></body></html>',
                encoding="utf-8",
            )

            with patch.dict(
                os.environ,
                {"REASBOOK_SITE_ROOT": "/ReasBook/"},
                clear=False,
            ):
                self.assertEqual(verify._missing_internal_references(site), [])

    def test_pages_assembly_omits_version_links_without_version_archive(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoPaper",
            "slug": "demopaper",
            "branch": "v4.30.0",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            monolith = root / ".artifacts" / "monolith"
            docs = monolith / "docs" / "ReasBook" / "DemoPaper"
            pages = monolith / "papers" / "demopaper"
            docs.mkdir(parents=True)
            pages.mkdir(parents=True)
            html_page = "<!doctype html><html><body>content</body></html>"
            (docs / "Paper.html").write_text(html_page, encoding="utf-8")
            (pages / "index.html").write_text(html_page, encoding="utf-8")
            (pages / "section.html").write_text(html_page, encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            site = root / ".site"
            for page in (
                site / "index.html",
                site / "sites" / "demopaper" / "index.html",
                site / "docs" / "ReasBook" / "index.html",
            ):
                self.assertNotIn(
                    "Version Archive",
                    page.read_text(encoding="utf-8"),
                )

    def test_pages_assembly_normalizes_explicit_root_documentation(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "DemoTheory",
            "slug": "demotheory",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docs = root / ".artifacts" / "monolith" / "docs" / "ReasBook"
            (docs / "DemoTheory").mkdir(parents=True)
            (docs / "DemoTheory" / "Lemma.html").write_text("lemma", encoding="utf-8")
            (docs / "DemoTheory.html").write_text("paper", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            canonical = (
                root
                / ".site"
                / "docs"
                / "ReasBook"
                / "Papers"
                / "DemoTheory"
                / "Paper.html"
            )
            self.assertEqual(canonical.read_text(encoding="utf-8"), "paper")

    def test_pages_assembly_handles_explicit_root_file_without_directory(self) -> None:
        project = {
            "kind": "papers",
            "kindTitle": "Papers",
            "name": "RootOnly",
            "slug": "rootonly",
            "branch": "v4.32.2",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docs = root / ".artifacts" / "monolith" / "docs" / "ReasBook"
            docs.mkdir(parents=True)
            (docs / "RootOnly.html").write_text("paper", encoding="utf-8")

            values = {"PROJECTS_JSON": json.dumps([project])}
            with working_directory(root), patch.dict(os.environ, values, clear=False):
                assemble.main()

            canonical = (
                root
                / ".site"
                / "docs"
                / "ReasBook"
                / "Papers"
                / "RootOnly"
                / "Paper.html"
            )
            self.assertEqual(canonical.read_text(encoding="utf-8"), "paper")

    def test_publish_docs_uses_an_external_repository_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            docs = (
                repo / "ReasBook" / ".lake" / "build" / "reasbook-project-docs" / "doc"
            )
            site = repo / "ReasBookWeb" / "_site"
            project_docs = docs / "Books" / "DemoBook"
            project_docs.mkdir(parents=True)
            site.mkdir(parents=True)
            (project_docs / "Book.html").write_text("docs", encoding="utf-8")
            (site / "keep.txt").write_text("keep", encoding="utf-8")

            result = subprocess.run(
                [str(ROOT / "scripts" / "build" / "publish_docs.sh")],
                cwd=repo,
                env={**os.environ, "REASBOOK_REPO_ROOT": str(repo)},
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(
                (
                    site / "docs" / "ReasBook" / "Books" / "DemoBook" / "Book.html"
                ).is_file()
            )
            self.assertEqual((site / "keep.txt").read_text(encoding="utf-8"), "keep")

    def test_publish_docs_indexes_flat_project_layout(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "checkout"
            docs = (
                repo / "ReasBook" / ".lake" / "build" / "reasbook-project-docs" / "doc"
            )
            site = repo / "ReasBookWeb" / "_site"
            project_docs = docs / "DemoBook"
            project_docs.mkdir(parents=True)
            site.mkdir(parents=True)
            (project_docs / "Book.html").write_text("docs", encoding="utf-8")

            result = subprocess.run(
                [str(ROOT / "scripts" / "build" / "publish_docs.sh")],
                cwd=repo,
                env={
                    **os.environ,
                    "REASBOOK_REPO_ROOT": str(repo),
                    "REASBOOK_INCLUDE_PROJECTS": "books/DemoBook",
                },
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            index = (site / "docs" / "index.html").read_text(encoding="utf-8")
            self.assertIn("./ReasBook/DemoBook/Book.html", index)


if __name__ == "__main__":
    unittest.main()
