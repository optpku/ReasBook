"""Repeated generation must preserve the Lean source identity used by caches."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402


class SourceOverviewTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name) / "Chap01.lean"
        self.header = "/- Authors: Example Author -/\nimport Books.Example.Section01\n"

    def body(self, title):
        return [title, "",
                "This chapter aggregation page links to section overviews and source files.",
                "", "Verso links:", "- [Chapter overview](/ReasBook/chapter/)",
                "", "Section overviews:", "- Section 1", ""]

    def block(self, body):
        return "/-!\n" + "\n".join(body) + "\n-/\n"

    def update(self, body):
        with contextlib.redirect_stdout(io.StringIO()):
            generator.upsert_overview_block(self.path, body)
        return self.path.read_bytes()

    def test_custom_chapter_titles_are_byte_stable(self):
        for title in ("Part I — Basic Concepts", "Introduction", "Chapter 01"):
            with self.subTest(title=title):
                self.path.write_text(self.header)
                first = self.update(self.body(title))
                modified = self.path.stat().st_mtime_ns
                for _ in range(3):
                    self.assertEqual(self.update(self.body(title)), first)
                    self.assertEqual(self.path.stat().st_mtime_ns, modified)

    def test_accumulated_duplicates_are_removed_without_losing_authored_docs(self):
        authored = self.block(["Author's explanation", "Keep this mathematical motivation."])
        old = self.block(self.body("Part I — Basic Concepts"))
        self.path.write_text(self.header + old + authored + old + old + "\n#check Nat\n")
        result = self.update(self.body("Part I — Basic Concepts"))
        self.assertEqual(result.count(b"This chapter aggregation page"), 1)
        self.assertIn(authored.encode(), result)
        self.assertIn(b"#check Nat\n", result)
        self.assertEqual(self.update(self.body("Part I — Basic Concepts")), result)

    def test_legacy_overviews_are_replaced(self):
        for title in ("Overview page for Example.", "Chapter 01"):
            with self.subTest(title=title):
                self.path.write_text(self.header + self.block([title, "Verso links:", "old link"]))
                result = self.update(self.body("Replacement title"))
                self.assertNotIn(b"old link", result)
                self.assertEqual(result.count(b"/-!"), 1)

    def test_authored_navigation_is_not_mistaken_for_generator_output(self):
        for body in (["Basic Concepts", "Verso links:", "Section overviews:"],
                     ["Basic Concepts", "This chapter aggregation page links to section overviews and source files."]):
            with self.subTest(body=body):
                self.assertFalse(generator.is_generated_overview_block(body))


if __name__ == "__main__":
    unittest.main()
