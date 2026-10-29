"""Source-bound semantic selections, extraction coverage, and safe fallbacks."""

import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402
from reasbook_build_sdk.statement_docs import statement_excerpts, statement_source_url  # noqa: E402


class StatementHoverTests(unittest.TestCase):
    def test_remote_generator_syncs_snapshot_shell_without_replacing_version_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            tooling, target = Path(directory) / "tooling", Path(directory) / "version"
            for root in (tooling, target):
                (root / "static_files").mkdir(parents=True)
                (root / "ReasBookSite.lean").write_text("old shell")
                (root / "static_files/style.css").write_text("old styles")
            header = "/- Authors: Verified UI Author -/\n"
            (tooling / "ReasBookSite.lean").write_text(header + "new shell")
            (tooling / "static_files/style.css").write_text("new styles")
            compatibility = target / "LiterateModule.lean"
            compatibility.write_text("version-pinned compatibility")
            generator.sync_reader_shell(tooling, target)
            self.assertEqual((target / "ReasBookSite.lean").read_text(), header + "new shell")
            self.assertEqual((target / "static_files/style.css").read_text(), "new styles")
            self.assertEqual(compatibility.read_text(), "version-pinned compatibility")
            before = (target / "ReasBookSite.lean").stat().st_mtime_ns
            generator.sync_reader_shell(tooling, target)
            self.assertEqual((target / "ReasBookSite.lean").stat().st_mtime_ns, before)
            (target / "static_files/style.css").unlink()
            (target / "static_files/style.css").symlink_to(tooling / "static_files/style.css")
            (tooling / "ReasBookSite.lean").write_text("must not copy before validation")
            with self.assertRaisesRegex(ValueError, "symlink"):
                generator.sync_reader_shell(tooling, target)
            self.assertEqual((target / "ReasBookSite.lean").read_text(), header + "new shell")

    def test_source_links_follow_selected_heading_not_helper_or_context(self):
        source = ('/- 作者 -/\nnamespace Demo\nvariable (α : Type)\n'
                  '/-- Helper for Definition 1.1 -/\ndef helper := 0\n'
                  '/-- Definition 1.1: an auxiliary state. -/\n'
                  'structure State where\n  value : α\nend Demo\n')
        url = 'https://github.com/acme/book/blob/' + 'a' * 40 + '/Item.lean'
        selected = statement_excerpts(source, label='Definition 1.1')[0]
        self.assertEqual(statement_source_url(source, url + '#L1', selected), url + '#L7-L8')
        lines = generator.statement_blocks(source, 'Definition 1.1',
                                            f'[Documentation](docs) ([Lean source]({url}))',
                                            'definition-1-1', source_path='Item.lean')
        self.assertIn(f'[Lean source]({url}#L7-L8)', '\n'.join(lines))
        self.assertIn('.lean#L1)', '\n'.join(lines), 'attribution must keep the source header')
        with self.assertRaisesRegex(ValueError, 'does not match'):
            statement_source_url('\n' + source, url, selected)

    def test_source_links_for_recall_check_and_multiple_declarations(self):
        source = 'universe u\nrecall Nat.add_comm (a b : Nat) : a + b = b + a\n#check (ℕ → ℝ)\n'
        excerpts = statement_excerpts(source)
        self.assertEqual(statement_source_url(source, 'source', excerpts[0]), 'source#L2')
        self.assertEqual(statement_source_url(source, 'source', excerpts[1]), 'source#L3')
        text = '\n'.join(generator.statement_blocks(source, 'Statements',
                        '[Lean source](source)', 'items', limit=None, source_path='Item.lean'))
        self.assertIn('[Lean source](source#L2)', text)
        self.assertIn('Item.lean#L3)', text)

    def test_recall_support_preserves_version_extractor_and_rejects_ambiguous_hooks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            generator.write_recall_support(root)  # Source-only fixtures.
            path = root / 'LiterateExtract.lean'
            original = ('-- version-specific compatibility code\n'
                        'unsafe def go (args : Unit) := do\n'
                        '    let res ← Compat.Frontend.processCommands headerStx pctx cmdSt\n'
                        '    let res := res.updateLeading contents\n'
                        '    let env := (← cmdSt.get).commandState.env\n')
            path.write_text(original)
            generator.write_recall_support(root)
            result = path.read_text()
            self.assertTrue(result.startswith('-- version-specific compatibility code\n'))
            self.assertIn('info.runMetaM', result)
            self.assertIn('realizeGlobalConstNoOverload id', result)
            self.assertIn('reasbookRecallCodes reasbookParsed contents hls', result)
            self.assertLess(result.index('let reasbookParsed := res'), result.index('res.updateLeading contents'))
            generator.write_recall_support(root)
            self.assertEqual(result, path.read_text())
            hook = re.search(r'-- BEGIN REASBOOK RECALL HOOK\n.*?-- END REASBOOK RECALL HOOK\n',
                             result, flags=re.S).group(0)
            # Earlier preview iterations inserted a pre-highlighting hook.
            # Updating support must relocate it, not reference hls too early.
            moved = result.replace(hook, '').replace('    let res ←', hook + '    let res ←')
            path.write_text(moved)
            generator.write_recall_support(root)
            self.assertEqual(result, path.read_text())
            path.write_text(result + '\n-- BEGIN REASBOOK RECALL HOOK')
            with self.assertRaisesRegex(ValueError, 'ambiguous'):
                generator.write_recall_support(root)
            path.write_text('-- unknown extractor\n')
            with self.assertRaisesRegex(ValueError, 'unsupported Lean extractor'):
                generator.write_recall_support(root)

    def test_version_styles_are_preserved_and_shared_hover_styles_are_idempotent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            css = root / 'static_files/style.css'
            css.parent.mkdir()
            original = '/* version-specific theme */\nbody { color: #25232d; }\n'
            css.write_text(original)
            generator.write_statement_styles(root)
            first = css.read_text()
            self.assertTrue(first.startswith(original))
            self.assertIn('code.hl.lean.block', first)
            self.assertIn('.reader-contributors', first)
            self.assertIn('overflow-x: auto', first)
            self.assertIn('--verso-code-keyword-color:', first)
            self.assertIn('--verso-code-const-color:', first)
            self.assertIn('--verso-code-var-color:', first)
            self.assertIn('.tippy-box .hl.lean', first)
            generator.write_statement_styles(root)
            self.assertEqual(first, css.read_text())
            css.write_text(first + '\n/* BEGIN REASBOOK STATEMENT READER */')
            with self.assertRaisesRegex(ValueError, 'ambiguous'):
                generator.write_statement_styles(root)

    def test_ranges_preserve_unicode_context_scopes_and_selected_heading(self):
        source = ('/- 作者 -/\nnamespace Demo\nvariable (α : Type)\n'
                  '/-- Helper for Theorem 1.1. -/\nlemma helper : True := by trivial\n'
                  'section\nvariable (x : α)\n'
                  '/-- Theorem 1.1: an auxiliary object. -/\n'
                  '  theorem actual : x = x := by rfl\nend\n'
                  'theorem outside : True := by trivial\nend Demo\n')
        excerpts = statement_excerpts(source, label='Theorem 1.1')
        self.assertEqual(excerpts[0].name, 'actual')
        for excerpt in excerpts:
            self.assertEqual(tuple(source[a:b] for a, b in excerpt.source_ranges),
                             (*excerpt.context, excerpt.signature))
        outside = next(item for item in excerpts if item.name == 'outside')
        self.assertNotIn('variable (x : α)', outside.context)
        self.assertNotIn('by rfl', excerpts[0].signature)

    def test_structures_inductives_and_recall_keep_exact_ranges(self):
        source = ('structure Model where\n  field : Nat\n  law : field = field\n'
                  'inductive Choice where\n  | left : Choice\n  | right : Choice\n'
                  'recall Nat.add_comm (a b : Nat) : a + b = b + a\n'
                  '#check (fun x : Nat => x + 1)\n')
        for excerpt in statement_excerpts(source):
            self.assertEqual(tuple(source[a:b] for a, b in excerpt.source_ranges),
                             (*excerpt.context, excerpt.signature))

    def test_fence_binds_checked_module_source_ranges_and_identity(self):
        source = 'variable (x : Nat)\n/-- Theorem 1.1. -/\ntheorem example_thm : x = x := by rfl\n'
        lines = generator.statement_blocks(source, 'Theorem 1.1', '[Documentation](docs)',
                                            'theorem-1-1', module='Demo.Chap01.Theorem_1_1',
                                            source_path='ReasBook/Books/Demo/Chap01/Theorem_1_1.lean')
        opening = next(line for line in lines if ' reasbookStatement ' in line)
        record = json.loads(json.loads(opening.split(' reasbookStatement ', 1)[1]))
        self.assertEqual(record['module'], 'Demo.Chap01.Theorem_1_1')
        self.assertEqual(record['source_path'], 'Books/Demo/Chap01/Theorem_1_1.lean')
        self.assertRegex(record['source_sha256'], r'^[0-9a-f]{64}$')
        self.assertEqual('\n'.join(source[a:b] for a, b in record['ranges']),
                         'variable (x : Nat)\ntheorem example_thm : x = x')
        changed = generator.statement_blocks(source.replace('by rfl', 'by simp'),
                                            'Theorem 1.1', '[Documentation](docs)', 'theorem-1-1',
                                            module='Demo.Chap01.Theorem_1_1',
                                            source_path=record['source_path'])
        self.assertNotEqual(lines, changed, 'proof changes must invalidate the semantic input')

    def test_source_only_is_not_misrepresented_as_checked(self):
        lines = generator.statement_blocks('#check Nat\n', 'Statement',
                                            '— source only ([Lean source](source))', 'item',
                                            module='Demo.Legacy', source_path='Books/Demo/Legacy.lean')
        self.assertNotIn('reasbookStatement', '\n'.join(lines))
        self.assertIn('#check Nat', lines)

    def test_imports_and_locked_dependencies_invalidate_semantic_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Imported.lean').write_text('def value : Nat := 1\n')
            initial = generator.statement_environment_digest(root)
            (root / '.lake').mkdir()
            (root / '.lake/Cached.lean').write_text('not a source input')
            self.assertEqual(initial, generator.statement_environment_digest(root))
            (root / 'Imported.lean').write_text('def value : Int := 1\n')
            changed = generator.statement_environment_digest(root)
            self.assertNotEqual(initial, changed)
            (root / 'lake-manifest.json').write_text('{"rev":"updated"}')
            self.assertNotEqual(changed, generator.statement_environment_digest(root))

    def test_codegen_registers_semantic_modules_without_extra_reader_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = repo / 'ReasBook'
            item_dir = source / 'Books/Demo/Chap01'
            item_dir.mkdir(parents=True)
            (source / 'lakefile.lean').write_text('lean_lib Demo where\n  srcDir := "Books"\n')
            (source / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0\n')
            (item_dir.parent / 'Book.lean').write_text('import Demo.Chap01.Theorem_1_1\n')
            (item_dir / 'Theorem_1_1.lean').write_text('theorem actual : True := by trivial\n')
            (item_dir / 'Theorem_1_2.lean').write_text('theorem legacy : True := by trivial\n')
            inventories = generator.collect_chapter_inventories(source)
            entries = generator.collect_entries(source, inventories)
            readers = generator.collect_reader_chapters(entries, inventories)
            semantic = generator.write_work_pages(repo, source, entries, readers)
            self.assertIn('Demo.Chap01.Theorem_1_1', semantic)
            self.assertNotIn('Demo.Chap01.Theorem_1_2', semantic)
            self.assertNotIn('Demo.Chap01.Theorem_1_1', [entry.module for entry in entries])
            manifest = json.loads(generator.emit_literate_manifest(entries, semantic))
            self.assertIn('Demo.Chap01.Theorem_1_1', manifest['modules'])
            self.assertEqual(len(manifest['modules']), len(set(manifest['modules'])))
            paths = json.loads(generator.emit_literate_source_map(entries, source, semantic))
            self.assertEqual(paths['Demo.Chap01.Theorem_1_1'], 'Books/Demo/Chap01/Theorem_1_1.lean')
            chapter = (repo / 'ReasBookWeb/ReasBookSite/WorkPages/Books/Demo/Chap01.lean').read_text()
            self.assertIn('import ReasBookSite.StatementCode', chapter)
            self.assertIn('source only (outside the published documentation root)', chapter)
            self.assertNotIn('Theorem_1_2.html', chapter)
            self.assertEqual(len(re.findall(r'^`{3,} reasbookStatement ', chapter, re.M)), 1)
            self.assertTrue((repo / 'ReasBookWeb/ReasBookSite/StatementCode.lean').is_file())
            (source / 'Imported.lean').write_text('def value : Nat := 1\n')
            generator.write_work_pages(repo, source, entries, readers)
            changed = (repo / 'ReasBookWeb/ReasBookSite/WorkPages/Books/Demo/Chap01.lean').read_text()
            self.assertNotEqual(chapter, changed, 'import-only changes must rebuild native hover data')


if __name__ == '__main__':
    unittest.main()
