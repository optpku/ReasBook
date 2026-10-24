from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from reasbook_build_sdk import BuildFailed
from reasbook_build_sdk.statement_docs import enrich_documentation, source_reading


class StatementDocumentationTests(unittest.TestCase):
    def test_recall_keeps_comments_variables_and_multiline_statement(self):
        source = ('/- Authors: Test Author -/\nimport Mathlib\n\nuniverse u\n'
                  'open Path.Homotopic.Quotient\nvariable {X : Type u} [TopologicalSpace X]\n'
                  '/- Composition is well defined on homotopy classes. -/\n'
                  'recall mk_trans (f : Path x y) (g : Path y z) :\n'
                  '  mk (f.trans g) = (mk f).trans (mk g)\n')
        reading = source_reading(source)
        self.assertTrue(reading.references)
        self.assertFalse(reading.imports_only)
        self.assertEqual(reading.imports, ('Mathlib',))
        self.assertTrue(reading.body.startswith('universe u'))
        self.assertIn('variable {X : Type u}', reading.body)
        self.assertIn('Composition is well defined', reading.body)
        self.assertIn('recall mk_trans', reading.body)
        self.assertTrue(reading.body.endswith('mk (f.trans g) = (mk f).trans (mk g)'))

    def test_check_preserves_expression_and_does_not_invent_type(self):
        source = ('import Mathlib\nopen CategoryTheory\n'
                  'variable (C : Type u) [Category.{v} C]\n#check\n  TopCat ⥤ C\n')
        reading = source_reading(source)
        self.assertTrue(reading.references)
        self.assertEqual(reading.body, source.split('\n', 1)[1].strip())

    def test_comments_and_strings_do_not_create_references_or_imports(self):
        source = ('/- outer /- nested -/\nrecall fake : True\nimport Wrong\n-/\n'
                  'import Real -- #check fake\n'
                  'def exampleString := "hello\n#check fake\nimport Wrong"\n')
        reading = source_reading(source)
        self.assertFalse(reading.references)
        self.assertEqual(reading.imports, ('Real',))
        self.assertFalse(reading.imports_only)

    def test_imports_only_handles_module_public_imports_and_comments(self):
        reading = source_reading('\ufeffmodule\n/- note -/\npublic import A B\nimport C\n')
        self.assertTrue(reading.imports_only)
        self.assertEqual(reading.imports, ('A', 'B', 'C'))
        self.assertTrue(source_reading('/- no declarations -/').imports_only)

    def fixture(self, root, sources, *, contents=None, owners=None):
        doc = root / 'doc'
        doc.mkdir()
        (doc / 'style.css').write_text('body {}')
        module_sources = []
        urls = {}
        for module, source in sources.items():
            path = root / 'source' / Path(*module.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            module_sources.append((module, path))
            page = doc / Path(*module.split('.')).with_suffix('.html')
            page.parent.mkdir(parents=True, exist_ok=True)
            page.write_text('<html><body><main>' + (contents or {}).get(module, '') +
                            '</main><nav>existing navigation</nav></body></html>')
            urls[module] = f'https://github.com/test/repo/blob/{"a" * 40}/{path.name}'
        owners = owners or {module: frozenset({'Demo.Book'}) for module in sources}
        return doc, tuple(module_sources), owners, urls

    def test_enrichment_is_escaped_preserves_declarations_and_is_idempotent(self):
        with tempfile.TemporaryDirectory() as temp:
            source = 'import Mathlib\n/- <script>alert("bad")</script> -/\nrecall foo : 1 < 2\n'
            original = '<div class="decl" id="existing">Existing theorem</div>'
            args = self.fixture(Path(temp), {'Demo.Item': source}, contents={'Demo.Item': original})
            self.assertEqual(enrich_documentation(*args), 1)
            page = (args[0] / 'Demo/Item.html').read_text()
            self.assertIn('Statements</h2>', page)
            self.assertIn('recall foo : 1 &lt; 2', page)
            self.assertIn('&lt;script&gt;', page)
            self.assertNotIn('<script>', page)
            self.assertIn(original, page)
            self.assertIn(args[3]['Demo.Item'], page)
            self.assertEqual(args[1][0][1].read_text(), source)
            style = (args[0] / 'style.css').read_text()
            self.assertEqual(enrich_documentation(*args), 0)
            self.assertEqual((args[0] / 'style.css').read_text(), style)
            self.assertEqual((args[0] / 'Demo/Item.html').read_text(), page)

    def test_import_aggregators_link_directly_to_content_and_skip_empty_pages(self):
        with tempfile.TemporaryDirectory() as temp:
            args = self.fixture(Path(temp), {
                'Demo.Book': 'import Demo.Chap01\nimport Other.Book\n',
                'Demo.Chap01': 'import Demo.Section\nimport Demo.Empty\n',
                'Demo.Section': 'import Demo.Theorem_10\nimport Demo.Theorem_2\nimport Demo.Book\n',
                'Demo.Theorem_10': 'import Mathlib\nrecall foo : True\n',
                'Demo.Theorem_2': 'import Mathlib\n#check Nat\n',
                'Demo.Empty': 'import Mathlib\n',
                'Other.Book': 'import Mathlib\n#check Bool\n',
            }, owners={module: frozenset({owner}) for module, owner in (
                ('Demo.Book', 'Demo.Book'), ('Demo.Chap01', 'Demo.Book'),
                ('Demo.Section', 'Demo.Book'), ('Demo.Theorem_10', 'Demo.Book'),
                ('Demo.Theorem_2', 'Demo.Book'), ('Demo.Empty', 'Demo.Book'),
                ('Other.Book', 'Other.Book'),
            )})
            enrich_documentation(*args)
            page = (args[0] / 'Demo/Book.html').read_text()
            self.assertIn('href="Theorem_2.html"', page)
            self.assertIn('href="Theorem_10.html"', page)
            self.assertLess(page.index('Theorem_2.html'), page.index('Theorem_10.html'))
            for skipped in ('Chap01.html', 'Section.html', 'Empty.html', 'Other/Book.html', 'Mathlib.html'):
                self.assertNotIn(skipped, page)
            self.assertIn('No statements are published', (args[0] / 'Demo/Empty.html').read_text())

    def test_ordinary_declaration_pages_are_not_duplicated(self):
        with tempfile.TemporaryDirectory() as temp:
            args = self.fixture(Path(temp), {'Demo.Item': 'theorem foo : True := trivial'},
                                contents={'Demo.Item': '<div class="decl" id="foo">foo : True</div>'})
            path = args[0] / 'Demo/Item.html'
            original = path.read_text()
            self.assertEqual(enrich_documentation(*args), 0)
            self.assertEqual(path.read_text(), original)

    def test_missing_or_symlinked_pages_fail_instead_of_becoming_placeholders(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            args = self.fixture(root, {'Demo.Item': '#check Nat'})
            path = args[0] / 'Demo/Item.html'
            path.unlink()
            with self.assertRaises(BuildFailed):
                enrich_documentation(*args)
            outside = root / 'outside.html'
            outside.write_text('<main>untouched</main>')
            path.symlink_to(outside)
            with self.assertRaises(BuildFailed):
                enrich_documentation(*args)
            self.assertEqual(outside.read_text(), '<main>untouched</main>')


if __name__ == '__main__':
    unittest.main()
