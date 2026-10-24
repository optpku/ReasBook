from __future__ import annotations

from pathlib import Path
import re
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "pages"))

from reader_entrypoints import write_reader_entrypoints  # noqa: E402
from update_readme import resource_cell, update_resource_cells  # noqa: E402


class ReaderEntrypointsTests(unittest.TestCase):
    def test_catalogs_stay_on_site_and_project_content_is_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            catalogs = (
                "index.html", "books/index.html", "papers/index.html",
                "docs/index.html", "docs/ReasBook/index.html",
                "sites/demo/index.html", "versions/index.html",
                "versions/v4.30.0/index.html",
                "versions/v4.30.0/docs/index.html",
                "theorem-maps/index.html",
            )
            content = (
                "sites/demo/pages/index.html", "sites/demo/docs/index.html",
                "sites/demo/pages/chapter-1/index.html",
                "docs/ReasBook/Books/Demo/Book.html",
                "docs/ReasBook/Books/Demo/index.html",
                "versions/v4.30.0/books/demo/index.html",
                "versions/v4.30.0/docs/ReasBook/Demo/Book.html",
                "theorem-maps/books/demo/index.html", "static/catalog.css",
            )
            for relative in catalogs + content:
                path = site / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"original: {relative}", encoding="utf-8")
            changed = write_reader_entrypoints(site)
            self.assertEqual({p.relative_to(site).as_posix() for p in changed}, set(catalogs))
            for relative in catalogs:
                page = (site / relative).read_text(encoding="utf-8")
                if relative == 'sites/demo/index.html':
                    self.assertIn('content="0; url=pages/index.html"', page)
                else:
                    self.assertNotIn('http-equiv="refresh"', page)
                    self.assertIn('Statements and Documentation', page)
                    self.assertIn('<style>', page)
                    self.assertIn('class="catalog-list"', page)
                self.assertNotIn("original:", page)
            for relative in content:
                self.assertEqual((site / relative).read_text(), f"original: {relative}")
            self.assertEqual(write_reader_entrypoints(site), changed)

    def test_project_bookmarks_use_docs_when_reading_pages_are_absent(self):
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            project = site / 'versions/v4.30.0/sites/demo'
            docs = project / 'docs/index.html'
            docs.parent.mkdir(parents=True)
            docs.write_text('real documentation')
            (project / 'index.html').write_text('old project catalog')
            write_reader_entrypoints(site)
            self.assertIn('content="0; url=docs/index.html"', (project / 'index.html').read_text())
            self.assertEqual(docs.read_text(), 'real documentation')

    def test_catalog_skips_missing_artifacts_and_follows_local_redirects(self):
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            (site / 'sites/missing').mkdir(parents=True)
            (site / 'sites/missing/index.html').write_text('unpublished')
            (site / 'sites/demo/pages').mkdir(parents=True)
            (site / 'sites/demo/index.html').write_text('old catalog')
            (site / 'sites/demo/pages/index.html').write_text(
                '<meta http-equiv="refresh" content="0; url=../../../books/demo/">')
            target = site / 'books/demo/index.html'
            target.parent.mkdir(parents=True)
            target.write_text('<title>A readable book -- ReasBook</title><main>Statements</main>')
            write_reader_entrypoints(site)
            page = (site / 'index.html').read_text()
            self.assertIn('href="books/demo/index.html"', page)
            self.assertIn('A readable book', page)
            self.assertNotIn('sites/missing', page)
            self.assertIn('url=../../books/demo/index.html', (site / 'sites/demo/index.html').read_text())

    def test_readmes_link_to_project_resources_not_aggregate_catalogs(self):
        readmes = [ROOT / "README.md", ROOT / "README.zh-CN.md"]
        readmes.extend((ROOT / "ReasBook").rglob("README.md"))
        for readme in readmes:
            text = readme.read_text(encoding="utf-8")
            for path in re.findall(r"https://optpku\.github\.io/ReasBook/([^\s)]+)", text):
                with self.subTest(readme=readme.relative_to(ROOT), path=path):
                    self.assertRegex(
                        path,
                        r"^(?:docs/ReasBook/(?:Books|Papers)/[^/]+/(?:Book|Paper)\.html"
                        r"|sites/[^/]+/(?:pages|docs)/"
                        r"|theorem-maps/(?:books|papers)/[^/]+/(?:v[0-9]+/)?(?:\?view=(?:paper|lean))?"
                        r"|versions/v[0-9]+\.[0-9]+\.[0-9]+/"
                        r"(?:docs/[A-Za-z0-9_]+/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.html"
                        r"|(?:books|papers)/[^/]+/sections/[^/]+/))$",
                    )
            self.assertNotIn("https://optpku.github.io/ReasBook/)", text)
            self.assertNotIn("https://reasbook.reaslab.io/ReasBook", text)
            self.assertNotIn("https://reasbook-reviewer.reaslab.io", text)
            for path in re.findall(r"https://reasbook[.]reaslab[.]io([^\s)\[\]<>\"']*)", text):
                self.assertRegex(
                    path,
                    r"^(?:/?|/review/(?:books/[^/]+/)?|/artifacts/(?:projects/[^/]+/(?:"
                    r"docs/ReasBook/.+[.]html|(?:books|papers)/[^/]+/(?:sections/[^/]+/)?"
                    r"|glowinski_admm_counterexample/paper/"
                    r"|theorem-maps/(?:books|papers)/[^/]+/(?:v[0-9]+/)?(?:\?view=(?:paper|lean))?)?)?)$",
                )

    def test_bilingual_readmes_introduce_public_review_before_toolchains(self):
        for filename, heading, toolchains in (
            ("README.md", "## Online reading and review", "## Toolchain Branches"),
            ("README.zh-CN.md", "## 在线阅读与评审", "## 工具链分支"),
        ):
            with self.subTest(filename=filename):
                text = (ROOT / filename).read_text(encoding="utf-8")
                self.assertLess(text.index(heading), text.index(toolchains))
                introduction = text.split(heading, 1)[1].split("\n## ", 1)[0]
                for url in ("https://reasbook.reaslab.io/", "https://reasbook.reaslab.io/review/",
                            "https://reasbook.reaslab.io/artifacts/"):
                    self.assertIn(f"]({url})", introduction)
                for feature in ("Lean", "Docs", "Verso", "ReasLab"):
                    self.assertIn(feature, introduction)

    def test_public_review_platform_is_listed_and_has_app_documentation(self):
        for filename in ("README.md", "README.zh-CN.md"):
            with self.subTest(filename=filename):
                text = (ROOT / filename).read_text(encoding="utf-8")
                self.assertIn('<a href="https://reasbook.reaslab.io/">ReasBook Reviewer</a>', text)
        app = (ROOT / "apps/reasbook-reviewer/README.md").read_text(encoding="utf-8")
        for url in ("https://reasbook.reaslab.io/", "https://reasbook.reaslab.io/review/"):
            self.assertIn(f"]({url})", app)

    def test_published_paper_maps_survive_bilingual_readme_regeneration(self):
        for filename, language in (("README.md", "en"), ("README.zh-CN.md", "zh-CN")):
            original = (ROOT / filename).read_text(encoding="utf-8")
            for name in ("DFP_wolfe_local", "TR_LALM_theory", "glowinski_admm_counterexample"):
                with self.subTest(language=language, paper=name):
                    project = {"kind": "papers", "name": name, "slug": name.lower()}
                    url = (f"https://reasbook.reaslab.io/artifacts/projects/{name.lower()}/"
                           f"theorem-maps/papers/{name.lower()}/")
                    lines = original.splitlines()
                    index = next(i for i, line in enumerate(lines) if line.startswith("| **[") and f"ReasBook/Papers/{name}/" in line)
                    end = index + 1
                    while end < len(lines) and lines[end].startswith("| ↳ **"):
                        end += 1
                    block = "\n".join(lines[index:end])
                    self.assertIn(url, block)
                    if name != "DFP_wolfe_local":
                        self.assertIn(url, resource_cell(project, language=language))
                    with tempfile.TemporaryDirectory() as temp:
                        readme = Path(temp) / filename
                        readme.write_text(original, encoding="utf-8")
                        update_resource_cells(readme, {("papers", name): project}, language=language)
                        self.assertIn(url, readme.read_text(encoding="utf-8"))
                        if end > index + 1:
                            self.assertIn(block, readme.read_text(encoding="utf-8"))

    def test_regeneration_keeps_original_papers_and_source_notes(self):
        projects = {
            ("papers", name): {"kind": "papers", "name": name, "slug": name.lower()}
            for name in ("DFP_wolfe_local", "RockafellarSum_2026", "BFGSMinimumQOrder_Liu_2026")
        }
        for filename, language in (("README.md", "en"), ("README.zh-CN.md", "zh-CN")):
            with self.subTest(language=language), tempfile.TemporaryDirectory() as temp:
                original = (ROOT / filename).read_text(encoding="utf-8")
                readme = Path(temp) / filename
                readme.write_text(original, encoding="utf-8")
                update_resource_cells(readme, projects, language=language)
                regenerated = readme.read_text(encoding="utf-8")
                self.assertEqual(regenerated, original)
                self.assertIn("https://arxiv.org/html/2608.21708v1", regenerated)
                self.assertIn("note/rockafellar_sum_technical_note.pdf", regenerated)
                self.assertIn("note/rockafellar_sum_technical_note.tex", regenerated)
                self.assertEqual(update_resource_cells(readme, projects, language=language), 0)

    def test_published_docs_use_the_actual_module_entry_points(self):
        for name, entry in (
            ("BFGSMinimumQOrder_Liu_2026", "ReasBook/BFGSMinimumQOrder_Liu_2026.html"),
            ("TR_LALM_theory", "ReasBook/TR_LALM_theory.html"),
            ("glowinski_admm_counterexample", "ReasBook/glowinski_admm_counterexample/Paper.html"),
        ):
            with self.subTest(project=name):
                resource = resource_cell({"kind": "papers", "name": name, "slug": name.lower()})
                self.assertIn(f"/projects/{name.lower()}/docs/{entry}", resource)
                self.assertNotIn("/sites/", resource)

    def test_rejects_symlinked_catalog_outside_site(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            site = root / "site"
            site.mkdir()
            outside = root / "outside.html"
            outside.write_text("untouched")
            (site / "index.html").symlink_to(outside)
            with self.assertRaises(ValueError):
                write_reader_entrypoints(site)
            self.assertEqual(outside.read_text(), "untouched")


if __name__ == "__main__":
    unittest.main()
