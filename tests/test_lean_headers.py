"""Dependency-free header and generator regression checks for every version branch."""

from __future__ import annotations

import ast
import importlib.util
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import lean_headers  # noqa: E402

spec = importlib.util.spec_from_file_location("author_checker", ROOT / "scripts/config/check_lean_authors.py")
assert spec and spec.loader
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def generator_functions() -> dict:
    path = ROOT / "ReasBookWeb/scripts/gen_sections.py"
    tree = ast.parse(path.read_text(encoding="utf-8"))
    selected = [node for node in tree.body if (
        isinstance(node, ast.FunctionDef) and node.name in {
            "with_generated_lean_header", "generated_body_first_line", "write_text_if_changed"
        }
    ) or (
        isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "GENERATED_LEAN_HEADER"
            for target in node.targets
        )
    )]
    scope = {"Path": Path, "os": os, "tempfile": tempfile, "re": re,
             "header_span": lean_headers.header_span, "author_field": lean_headers.author_field}
    exec(compile(ast.Module(body=selected, type_ignores=[]), str(path), "exec"), scope)
    return scope


class LeanHeaderRegressionTests(unittest.TestCase):
    def test_span_preserves_nested_comments_and_bom(self) -> None:
        source = "\ufeff  \n/-\nA /- nested /- note -/ -/\nAuthors: Ada Lovelace\n-/\nmodule\n"
        start, end = lean_headers.header_span(source)
        self.assertEqual(source[:start], "\ufeff  \n")
        self.assertEqual(source[end:], "\nmodule\n")
        self.assertEqual(lean_headers.opening_header(source), source[start:end])

    def test_documentation_and_incomplete_comments_are_not_headers(self) -> None:
        for source in ("/-! Docs -/", "/-- Declaration -/", "/- incomplete", "module\n/- note -/"):
            with self.subTest(source=source):
                self.assertIsNone(lean_headers.header_span(source))

    def test_author_field_ignores_nested_examples_and_checks_continuations(self) -> None:
        header = "/-\n/-\nAuthors: An Example\n-/\nAuthors: Ada Lovelace,\n  Grace Hopper\n-/"
        self.assertEqual(lean_headers.author_field(header), "Ada Lovelace, Grace Hopper")
        self.assertIsNone(lean_headers.author_field("/-\n/-\nAuthors: Example\n-/\n-/"))
        with self.assertRaises(ValueError):
            lean_headers.author_field("/-\nAuthors: Ada\nAuthors: Grace\n-/")

    def test_author_checker_accepts_names_and_rejects_placeholder_entries(self) -> None:
        for name in ("Claude Shannon", "Jean-Claude", "王子辰", "Ada Lovelace, Grace Hopper"):
            self.assertIsNone(checker.author_error(f"/-\nAuthors: {name}\n-/"), name)
        for name in ("???", "---", "123", "Codex", "Ada Lovelace, Codex", "Unknown", "<name>"):
            self.assertIsNotNone(checker.author_error(f"/-\nAuthors: {name}\n-/"), name)

    def test_generation_retains_exact_header_and_owner_marker(self) -> None:
        functions = generator_functions()
        body = "-- Generated owner marker\nimport VersoBlog\n"
        for prefix in ("", "\ufeff", "\ufeff  \n"):
            notice = prefix + (
                "/-\nCopyright (c) 2024 Original Owner.\nA /- nested note -/\n"
                "Authors: Ada Lovelace,\n  Grace Hopper\nRetain this notice.\n-/"
            )
            previous = notice + "\n\n" + body
            revised = functions["with_generated_lean_header"](body, previous)
            self.assertEqual(revised, previous)
            self.assertIsNone(checker.author_error(revised))
            self.assertEqual(functions["with_generated_lean_header"](previous, None), previous)
            if "generated_body_first_line" in functions:
                with tempfile.TemporaryDirectory() as temp:
                    page = Path(temp) / "Owned.lean"
                    page.write_text(revised, encoding="utf-8")
                    self.assertEqual(functions["generated_body_first_line"](page), ["-- Generated owner marker"])

    def test_new_bom_file_keeps_bom_at_start(self) -> None:
        revised = generator_functions()["with_generated_lean_header"]("\ufeffimport VersoBlog\n", None)
        self.assertTrue(revised.startswith("\ufeff/-"))
        self.assertEqual(revised.count("\ufeff"), 1)
        self.assertIsNone(checker.author_error(revised))

    def test_broken_header_does_not_overwrite_original_file(self) -> None:
        writer = generator_functions()["write_text_if_changed"]
        with tempfile.TemporaryDirectory() as temp:
            page = Path(temp) / "Broken.lean"
            original = "/-\nAuthors: Ada Lovelace\n"
            page.write_text(original, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unterminated"):
                writer(page, "import VersoBlog\n", log=False)
            self.assertEqual(page.read_text(encoding="utf-8"), original)


if __name__ == "__main__":
    unittest.main()
