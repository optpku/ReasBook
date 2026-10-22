from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts/config/check_lean_authors.py"
spec = importlib.util.spec_from_file_location("check_lean_authors", CHECKER)
assert spec and spec.loader
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections  # noqa: E402


class LeanAuthorTests(unittest.TestCase):
    def test_opening_header_requires_real_nonempty_author_list(self) -> None:
        valid = "/-\nCopyright (c) 2026 Ada.\nAuthors: Ada Lovelace, Grace Hopper\n-/\n"
        self.assertIsNone(checker.author_error(valid + "module\nimport Mathlib\n"))
        self.assertIsNone(checker.author_error("\ufeff  " + valid))
        self.assertIsNone(checker.author_error(valid.replace("Authors:", "  Authors:")))
        for source in (
            "import Mathlib\n" + valid,
            "/-!\nAuthors: Ada Lovelace\n-/\n",
            "/--\nAuthors: Ada Lovelace\n-/\n",
            "/-\nAuthors: \n-/\n",
            "/-\nAuthor: Ada Lovelace\n-/\n",
            "/-\nAuthors: <name>\n-/\n",
            "/-\nAuthors: TODO\n-/\n",
            "/-\nAuthors: Codex\n-/\n",
            "/-\nAuthors: Ada Lovelace, Codex\n-/\n",
            "/-\nAuthors: ???\n-/\n",
            "/-\nAuthors: ---\n-/\n",
            "/-\nAuthors: 1234\n-/\n",
            "/-\nAuthors: Ada Lovelace\nAuthors: Grace Hopper\n-/\n",
            "/-\nAuthors: TR-LALM formalization contributors\n-/\n",
            "/-\nAuthors: Ada Lovelace, \n-/\n",
            "/-\nAuthors: Ada Lovelace.\n-/\n",
            "/-\nAuthors: Ada Lovelace\n",
        ):
            with self.subTest(source=source):
                self.assertIsNotNone(checker.author_error(source))

    def test_human_names_are_not_confused_with_model_labels(self) -> None:
        for names in ("Claude Shannon", "Jean-Claude Van Damme", "王子辰", "O'Neill, Jean-Paul"):
            with self.subTest(names=names):
                self.assertIsNone(checker.author_error(f"/-\nAuthors: {names}\n-/\nmodule\n"))

    def test_author_metadata_is_not_taken_from_nested_examples(self) -> None:
        source = "/-\nExample /-\nAuthors: Fake Example\n-/\n-/\nmodule\n"
        self.assertIsNotNone(checker.author_error(source))
        source = "/-\nExample /-\nAuthors: Fake Example\n-/\nAuthors: Ada Lovelace\n-/\n"
        self.assertIsNone(checker.author_error(source))

    def test_wrapped_author_list_is_checked_in_full(self) -> None:
        self.assertIsNone(checker.author_error("/-\nAuthors: Ada Lovelace,\n  Grace Hopper\n-/\n"))
        self.assertIsNotNone(checker.author_error("/-\nAuthors: Ada Lovelace,\n  ???\n-/\n"))
        self.assertIsNotNone(checker.author_error("/-\nAuthors: Ada Lovelace,\n  Codex\n-/\n"))

    def test_nested_comment_does_not_terminate_header(self) -> None:
        source = "/-\nA /- nested note -/\nAuthors: Ada Lovelace\n-/\nmodule\n"
        self.assertIsNone(checker.author_error(source))
        self.assertEqual(checker.opening_header(source), source.split("\nmodule")[0])

    def test_working_tree_and_ref_audits_do_not_confuse_git_author_with_header(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            (repo / "Known.lean").write_text("/-\nAuthors: Ada Lovelace\n-/\nmodule\n")
            (repo / ".gitignore").write_text(".lake/\n")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(
                ["git", "-C", str(repo), "-c", "user.name=Someone Else",
                 "-c", "user.email=else@example.invalid", "commit", "-qm", "fixture"],
                check=True,
            )
            (repo / "New.lean").write_text("import Mathlib\n")
            (repo / ".lake").mkdir()
            (repo / ".lake/Vendor.lean").write_text("import Mathlib\n")
            current = dict(checker.lean_sources(repo))
            self.assertEqual(set(current), {"Known.lean", "New.lean"})
            pinned = dict(checker.lean_sources(repo, ref="HEAD"))
            self.assertEqual(set(pinned), {"Known.lean"})
            self.assertIn("Ada Lovelace", pinned["Known.lean"])
            self.assertIsNotNone(checker.author_error(current["New.lean"]))
            self.assertEqual(set(dict(checker.lean_sources(repo, paths=["New.lean"]))), {"New.lean"})

    def test_all_published_main_lean_sources_have_author_headers(self) -> None:
        sources = list(checker.lean_sources(ROOT))
        self.assertTrue(sources)
        failures = [(name, error) for name, source in sources if (error := checker.author_error(source))]
        self.assertEqual(failures, [])

    def test_generator_adds_headers_and_preserves_existing_notices(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            page = Path(temp) / "Generated.lean"
            body = gen_sections.GENERATED_READER_MARKER + "\nimport VersoBlog\n"
            gen_sections.write_text_if_changed(page, body, log=False)
            generated = page.read_text()
            self.assertIsNone(checker.author_error(generated))
            self.assertEqual(gen_sections.generated_body_first_line(page), [gen_sections.GENERATED_READER_MARKER])
            self.assertFalse(gen_sections.write_text_if_changed(page, body, log=False))
            original = (
                "/-\nCopyright (c) 2024 Ada Lovelace.\n"
                "Released under the original project license.\n"
                "Authors: Ada Lovelace\n-/\n\n"
            )
            page.write_text(original + body)
            gen_sections.write_text_if_changed(page, body + "-- Updated index\n", log=False)
            self.assertTrue(page.read_text().startswith(original))
            self.assertNotIn("Wanli Ma", page.read_text())
            self.assertEqual(gen_sections.generated_body_first_line(page), [gen_sections.GENERATED_READER_MARKER])
            legacy = original.replace("Authors: Ada Lovelace\n", "")
            page.write_text(legacy + body)
            gen_sections.write_text_if_changed(page, body + "-- Regenerated\n", log=False)
            self.assertIn("Copyright (c) 2024 Ada Lovelace.", page.read_text())
            self.assertIn("Released under the original project license.", page.read_text())
            self.assertIsNone(checker.author_error(page.read_text()))
            manual = Path(temp) / "Manual.lean"
            manual.write_text(original + "import VersoBlog\n")
            self.assertNotEqual(gen_sections.generated_body_first_line(manual), [gen_sections.GENERATED_READER_MARKER])
            markdown = Path(temp) / "README.md"
            gen_sections.write_text_if_changed(markdown, "# A page\n", log=False)
            self.assertEqual(markdown.read_text(), "# A page\n")

    def test_generator_retains_nested_bom_and_wrapped_header_metadata(self) -> None:
        body = gen_sections.GENERATED_READER_MARKER + "\nimport VersoBlog\n"
        for prefix in ("", "\ufeff", "\ufeff  \n"):
            for newline in ("\n", "\r\n"):
                notice = prefix + newline.join((
                    "/-", "Copyright (c) 2024 Original Owner.",
                    "A /- nested legal note /- with another level -/ -/",
                    "Authors: Ada Lovelace,", "  Grace Hopper", "Retain this notice.", "-/",
                ))
                with self.subTest(prefix=prefix, newline=newline):
                    previous = notice + "\n\n" + body
                    revised = gen_sections.with_generated_lean_header(body, previous)
                    self.assertTrue(revised.startswith(notice))
                    self.assertEqual(checker.opening_header(revised), checker.opening_header(previous))
                    self.assertIsNone(checker.author_error(revised))
                    self.assertEqual(gen_sections.with_generated_lean_header(previous, None), previous)
                    with tempfile.TemporaryDirectory() as temp:
                        page = Path(temp) / "Nested.lean"
                        page.write_text(revised)
                        self.assertEqual(gen_sections.generated_body_first_line(page), [gen_sections.GENERATED_READER_MARKER])

    def test_generator_does_not_discard_unterminated_existing_header(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            page = Path(temp) / "Broken.lean"
            original = "/-\nCopyright (c) 2024 Owner.\nAuthors: Ada Lovelace\n"
            page.write_text(original)
            with self.assertRaisesRegex(ValueError, "unterminated"):
                gen_sections.write_text_if_changed(page, "import VersoBlog\n", log=False)
            self.assertEqual(page.read_text(), original)


if __name__ == "__main__":
    unittest.main()
