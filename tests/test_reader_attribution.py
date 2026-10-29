from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402
import reader_attributions as renderer  # noqa: E402
from reasbook_sdk_common.attribution import project_key_from_url  # noqa: E402

HEADER = '''/-
Authors: Alice, Bob
Project-level attribution: optpku/ReasBook@1111111111111111111111111111111111111111:README.md (Contributors).
-/
'''


class ReaderAttributionTests(unittest.TestCase):
    def test_full_reading_titles_preserve_statement_numbering(self):
        self.assertEqual(generator.section_title_from_stem('Theorem_1_1'), 'Theorem 1.1')
        self.assertEqual(generator.section_title_from_stem('Lemma_2_3_Trajectory'), 'Lemma 2.3 Trajectory')
        self.assertEqual(generator.section_title_from_stem('section02_part3'), 'Section 02 -- Part 3')

    def test_file_header_scope_and_source_preserved(self):
        credit = generator.source_attribution(HEADER, "ReasBook/Books/Demo/Item.lean")
        self.assertEqual(credit["authors"], "Alice, Bob")
        self.assertEqual(credit["scope"], "project")
        self.assertEqual(credit["evidence_url"], "https://github.com/optpku/ReasBook/blob/" + "1" * 40 + "/README.md")
        self.assertTrue(credit["source_url"].endswith("ReasBook/Books/Demo/Item.lean#L1"))
        text = '\n'.join(generator.statement_blocks(HEADER + "theorem foo : True := by trivial",
                                                    "Theorem 1.1", "", "foo"))
        self.assertIn("Lean contributors (project-level attribution): Alice, Bob", text)
        self.assertNotIn("Lean authors: Wanli Ma", text)

    def test_file_level_headers_and_missing_headers_are_not_inferred(self):
        source = "/- Author: Original Author\n/- Authors: Fake Person -/\n-/\ndef x := 1"
        credit = generator.source_attribution(source, "")
        self.assertEqual(credit["authors"], "Original Author")
        self.assertEqual(credit["scope"], "file")
        text = '\n'.join(generator.source_attribution_blocks("def x := 1", ""))
        self.assertIn("Lean authors: not recorded", text)
        self.assertNotIn("Wang", text)

    def test_author_metadata_is_escaped_in_verso_and_html(self):
        source = "/- Authors: [Alice](bad), <script>alert(1)</script>\n-/"
        blocks = '\n'.join(generator.source_attribution_blocks(source, ""))
        self.assertIn(r"\[Alice\]", blocks)
        html = renderer.attribution_html(generator.source_attribution(source, ""))
        self.assertIn("&lt;script&gt;", html)
        self.assertNotIn("<script>", html)

    def test_annotation_follows_main_title_leaves_hover_bytes_untouched_and_is_idempotent(self):
        tail = '<code data-verso-hover="42">foo</code><script>let s = "</h1>";</script>'
        page = '<header><h1>Other title</h1></header><div class="main"><h1>Title</h1>' + tail + '</div>'
        credit = generator.source_attribution(HEADER, "ReasBook/Item.lean")
        result = renderer.annotate_page(page, credit)
        self.assertIn('<h1>Title</h1>' + renderer.BEGIN, result)
        self.assertIn(tail, result)
        self.assertEqual(renderer.annotate_page(result, credit), result)
        changed = renderer.annotate_page(result, {**credit, "authors": "Carol"})
        self.assertEqual(changed.count(renderer.BEGIN), 1)
        self.assertNotIn("Alice", changed)
        with self.assertRaisesRegex(ValueError, "title"):
            renderer.annotate_page('<h1>Outside main</h1>', credit)

    def test_invalid_targets_fail_before_any_writes_and_symlinks_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory) / "site"
            page = site / "valid/index.html"
            page.parent.mkdir(parents=True)
            original = '<main id="main-content"><h1>Title</h1></main>'
            page.write_text(original)
            manifest = Path(directory) / "manifest.json"
            credit = generator.source_attribution(HEADER, "")
            for bad in ("../outside/", "/absolute/", "missing/"):
                manifest.write_text(json.dumps(dict(schema_version=1, pages={"valid/": credit, bad: credit})))
                with self.assertRaises(ValueError):
                    renderer.apply_attributions(site, manifest)
                self.assertEqual(page.read_text(), original)
            (site / "alias").symlink_to(page.parent, target_is_directory=True)
            manifest.write_text(json.dumps(dict(schema_version=1, pages={"alias/": credit})))
            with self.assertRaises(ValueError):
                renderer.apply_attributions(site, manifest)
            manifest.write_text(json.dumps(dict(schema_version=1, pages={"valid/": credit})))
            self.assertEqual(renderer.apply_attributions(site, manifest), 1)
            self.assertIn("Alice", page.read_text())

    def test_route_manifest_credits_full_pages_not_generated_aggregations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Item.lean").write_text(HEADER)
            routes = [("part/", "Book.Demo.Item"), ("legacy/", "Book.Demo.Item"),
                      ("chapter/", "ReasBookSite.WorkPages.Books.Demo.Chap01")]
            result = json.loads(generator.emit_reader_attributions(root, routes, {"Demo.Item": "Item.lean"}))
            self.assertEqual(set(result["pages"]), {"part/", "legacy/"})
            self.assertEqual(result["pages"]["part/"]["authors"], "Alice, Bob")

    def test_catalog_identity_is_exact_not_fuzzy(self):
        slug = "firstordermethodsoptimization_beck_2017"
        key = "books/FirstOrderMethodsOptimization_Beck_2017"
        for url in (f"./sites/{slug}/", f"/versions/v4.30.0/books/{slug}/", f"projects/{slug}/",
                    f"docs/ReasBook/{slug}.html"):
            self.assertEqual(project_key_from_url(url), key)
        self.assertIsNone(project_key_from_url(f"sites/{slug}_different/"))
        self.assertIsNone(project_key_from_url("versions/"))


if __name__ == "__main__":
    unittest.main()
