"""Resolve native Verso input files independently of logical module names."""

from dataclasses import replace
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402


class LiterateSourcePathTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repo = Path(temporary.name)
        self.source = self.repo / "ReasBook"
        self.source.mkdir()
        self.web = self.repo / "ReasBookWeb"
        self.web.mkdir()

    def entry(self, module, category="papers", project="NestedPaper"):
        return generator.Entry(category, module, "Title", "route/", project,
                               0, 0, 0, module.rsplit(".", 1)[-1].lower())

    def source_file(self, relative):
        path = self.source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("/- Authors: Test Author -/\n#check Nat\n")
        return path

    def test_nested_explicit_roots_preserve_logical_literate_names(self):
        (self.source / "lakefile.lean").write_text(
            'lean_lib Implementation where\n'
            '  srcDir := "Papers/NestedPaper"\n'
            '  roots := #[`Book, `Paper]\n'
            'lean_lib NestedPaper where\n'
            '  srcDir := "Papers"\n'
            '  roots := #[`NestedPaper]\n'
        )
        self.source_file("Papers/NestedPaper/Book/Algorithm_2_1.lean")
        self.source_file("Papers/NestedPaper/Paper.lean")
        self.source_file("Papers/NestedPaper.lean")
        entries = [self.entry(name) for name in
                   ("Book.Algorithm_2_1", "Paper", "NestedPaper")]
        mapping = json.loads(generator.emit_literate_source_map(entries, self.source))
        self.assertEqual(mapping, {
            "Book.Algorithm_2_1": "Papers/NestedPaper/Book/Algorithm_2_1.lean",
            "Paper": "Papers/NestedPaper/Paper.lean",
            "NestedPaper": "Papers/NestedPaper.lean",
        })
        self.assertEqual(json.loads(generator.emit_literate_manifest(entries))["modules"],
                         [entry.module for entry in entries])

    def test_aggregate_and_flat_layouts_are_resolved(self):
        for aggregate in (True, False):
            with self.subTest(aggregate=aggregate):
                generator._lake_source_layout.cache_clear()
                generator._detect_layout.cache_clear()
                (self.source / "lakefile.lean").write_text(
                    'lean_lib Books where\n' if aggregate else
                    'lean_lib Demo where\n  srcDir := "Books"\n'
                )
                self.source_file("Books/Demo/Chap01/Section01.lean")
                module = ("Books." if aggregate else "") + "Demo.Chap01.Section01"
                result = json.loads(generator.emit_literate_source_map(
                    [self.entry(module, "books", "Demo")], self.source))
                self.assertEqual(result[module], "Books/Demo/Chap01/Section01.lean")

    def test_missing_duplicate_and_escaping_sources_fail_closed(self):
        (self.source / "lakefile.lean").write_text('lean_lib Papers where\n')
        entry = self.entry("Papers.NestedPaper.Paper")
        with self.assertRaisesRegex(ValueError, "missing literate source"):
            generator.emit_literate_source_map([entry], self.source)
        path = self.source_file("Papers/NestedPaper/Paper.lean")
        with self.assertRaisesRegex(ValueError, "duplicate literate module"):
            generator.emit_literate_source_map([entry, replace(entry)], self.source)
        path.unlink()
        outside = self.repo / "outside.lean"
        outside.write_text("#check Nat\n")
        path.symlink_to(outside)
        with self.assertRaises(ValueError):
            generator.emit_literate_source_map([entry], self.source)

    def test_ambiguous_logical_sources_are_not_silently_overwritten(self):
        (self.source / "lakefile.lean").write_text(
            'lean_lib First where\n  srcDir := "Papers/NestedPaper/A"\n'
            'lean_lib Second where\n  srcDir := "Papers/NestedPaper/B"\n'
        )
        self.source_file("Papers/NestedPaper/A/Item.lean")
        self.source_file("Papers/NestedPaper/B/Item.lean")
        with self.assertRaisesRegex(ValueError, "ambiguous literate source"):
            generator.emit_literate_source_map([self.entry("Item")], self.source)

    def test_web_lakefile_rewrite_preserves_headers_and_json_paths(self):
        original = (ROOT / "ReasBookWeb/lakefile.lean").read_text()
        prefix = '    let origName := "/".intercalate (module.components.map (·.toString)) ++ ".lean"\n'
        direct = "    let origLeanFile : System.FilePath := pkg.dir / reasbookRoot / origName\n"
        trace = "    addTrace (← computeTrace <| TextFilePath.mk origLeanFile)\n"
        baseline = prefix + direct + trace
        flat = (prefix + '    let papersPath := pkg.dir / reasbookRoot / "Papers" / origName\n'
                + '    let booksPath := pkg.dir / reasbookRoot / "Books" / origName\n'
                + '    let origLeanFile ← if (← papersPath.pathExists) then pure papersPath else pure booksPath\n'
                + trace)
        optional = (prefix + direct
                    + '    -- Explicit project roots can place a module below `Papers/<project>` or\n'
                    + '    -- `Books/<project>`, so its logical module path need not be a source path\n'
                    + '    -- relative to `ReasBook`.  The literate JSON is the authoritative input;\n'
                    + '    -- retain the source trace when the legacy flat path exists.\n'
                    + '    if ← origLeanFile.pathExists then\n  ' + trace)
        self.assertIn(baseline, original)
        lakefile = self.web / "lakefile.lean"
        for block in (baseline, flat, optional):
            lakefile.write_text(original.replace(baseline, block))
            generator.update_literate_source_lookup(self.web)
            rewritten = lakefile.read_text()
            self.assertTrue(rewritten.startswith(original.split("import Lake", 1)[0]))
            self.assertIn('let jsonName := "/".intercalate', rewritten)
            self.assertIn('let sourcePaths ← match Lean.Json.parse sourcePathsText', rewritten)
            self.assertIn('addTrace (← computeTrace <| TextFilePath.mk sourcePathsFile)', rewritten)
            self.assertNotIn('let papersPath', rewritten)
            generator.update_literate_source_lookup(self.web)
            self.assertEqual(lakefile.read_text(), rewritten)
        malformed = rewritten.replace('"Missing source path', '"Changed source path')
        lakefile.write_text(malformed)
        with self.assertRaisesRegex(ValueError, "unrecognized generated"):
            generator.update_literate_source_lookup(self.web)
        self.assertEqual(lakefile.read_text(), malformed)

    def test_unknown_native_lookup_is_not_rewritten(self):
        lakefile = self.web / "lakefile.lean"
        original = "import Lake\n-- unfamiliar generator\n"
        lakefile.write_text(original)
        with self.assertRaisesRegex(ValueError, "unrecognized Web Lakefile"):
            generator.update_literate_source_lookup(self.web)
        self.assertEqual(lakefile.read_text(), original)


if __name__ == "__main__":
    unittest.main()
