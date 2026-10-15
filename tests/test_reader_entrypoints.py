from __future__ import annotations

from pathlib import Path
import re
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "pages"))

from reader_entrypoints import README_URL, write_reader_entrypoints  # noqa: E402
from update_readme import resource_cell, update_resource_cells  # noqa: E402


class ReaderEntrypointsTests(unittest.TestCase):
    def test_only_catalog_indexes_redirect_and_content_is_preserved(self):
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
                self.assertIn(f'content="0; url={README_URL}"', page)
                self.assertIn('content="noindex,follow"', page)
                self.assertIn(f'<a href="{README_URL}">', page)
                self.assertNotIn("original:", page)
            for relative in content:
                self.assertEqual((site / relative).read_text(), f"original: {relative}")
            self.assertEqual(write_reader_entrypoints(site), changed)

    def test_readmes_link_to_published_reaslab_resources(self):
        readmes = [ROOT / "README.md", ROOT / "README.zh-CN.md"]
        readmes.extend((ROOT / "ReasBook").rglob("README.md"))
        for readme in readmes:
            text = readme.read_text(encoding="utf-8")
            self.assertNotIn("https://optpku.github.io/ReasBook/", text)
            for path in re.findall(r"https://reasbook\.reaslab\.io/ReasBook/([^\s)]*)", text):
                with self.subTest(readme=readme.relative_to(ROOT), path=path):
                    self.assertRegex(
                        path,
                        r"^(?:projects/[^/]+/(?:docs/ReasBook/.+\.html"
                        r"|theorem-maps/(?:books|papers)/[^/]+/)?|)$",
                    )

    def test_published_paper_maps_survive_bilingual_readme_regeneration(self):
        for filename, language in (("README.md", "en"), ("README.zh-CN.md", "zh-CN")):
            original = (ROOT / filename).read_text(encoding="utf-8")
            for name in ("DFP_wolfe_local", "TR_LALM_theory"):
                with self.subTest(language=language, paper=name):
                    project = {"kind": "papers", "name": name, "slug": name.lower()}
                    url = f"https://reasbook.reaslab.io/ReasBook/projects/{name.lower()}/theorem-maps/papers/{name.lower()}/"
                    row = next(line for line in original.splitlines() if line.startswith("| **[") and f"ReasBook/Papers/{name}/" in line)
                    self.assertIn(url, row)
                    self.assertIn(url, resource_cell(project, language=language))
                    with tempfile.TemporaryDirectory() as temp:
                        readme = Path(temp) / filename
                        readme.write_text(original, encoding="utf-8")
                        update_resource_cells(readme, {("papers", name): project}, language=language)
                        self.assertIn(url, readme.read_text(encoding="utf-8"))

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
            ("BFGSMinimumQOrder_Liu_2026", "ReasBook/Paper.html"),
            ("TR_LALM_theory", "ReasBook/TR_LALM_theory.html"),
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
