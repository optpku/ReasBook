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
                        r"|theorem-maps/(?:books|papers)/[^/]+/)$",
                    )
            self.assertNotIn("https://optpku.github.io/ReasBook/)", text)

    def test_published_paper_maps_survive_bilingual_readme_regeneration(self):
        for filename, language in (("README.md", "en"), ("README.zh-CN.md", "zh-CN")):
            original = (ROOT / filename).read_text(encoding="utf-8")
            for name in ("DFP_wolfe_local", "TR_LALM_theory"):
                with self.subTest(language=language, paper=name):
                    project = {"kind": "papers", "name": name, "slug": name.lower()}
                    url = f"https://optpku.github.io/ReasBook/theorem-maps/papers/{name.lower()}/"
                    row = next(line for line in original.splitlines() if line.startswith("| **[") and f"ReasBook/Papers/{name}/" in line)
                    self.assertIn(url, row)
                    self.assertIn(url, resource_cell(project, language=language))
                    with tempfile.TemporaryDirectory() as temp:
                        readme = Path(temp) / filename
                        readme.write_text(original, encoding="utf-8")
                        update_resource_cells(readme, {("papers", name): project}, language=language)
                        self.assertIn(url, readme.read_text(encoding="utf-8"))

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
