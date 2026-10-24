from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from reasbook_build_sdk import BuildFailed
from reasbook_build_sdk.statement_docs import enrich_documentation, source_reading, statement_excerpts


class StatementDocumentationTests(unittest.TestCase):
    def test_numbered_headings_outrank_mentions_and_helpers(self):
        for heading in ('Lemma 2.5.5', 'Lemma 2-5-5', 'Chapter10 Lemma 2-5.5'):
            with self.subTest(heading=heading):
                source = ('/-- Helper for Lemma 2.5.5. -/\nlemma helper : True := by trivial\n'
                          '/-- Auxiliary result for Lemma 2.5.5. -/\nlemma aux : True := by trivial\n'
                          '/-- Uses Lemma 2.5.5. -/\nlemma citation : True := by trivial\n'
                          '/-- Lemma 2.5.50 is a different item. -/\nlemma other : True := by trivial\n'
                          f'/-- {heading}: the actual statement. -/\nlemma actual : True := by trivial\n')
                excerpts = statement_excerpts(source, label='Lemma 2.5.5')
                self.assertEqual(excerpts[0].signature, 'lemma actual : True')
                self.assertEqual(excerpts[1].signature, 'lemma citation : True')
                self.assertEqual(excerpts[2].signature, 'lemma other : True')
                self.assertEqual({item.signature for item in excerpts[-2:]},
                                 {'lemma helper : True', 'lemma aux : True'})

    def test_beck_definition_of_auxiliary_state_outranks_simp_helper(self):
        # Regression: Beck Chap14/Definition_14_1. Mathematical use of
        # "auxiliary" in the numbered definition must not penalize its heading.
        source = ('/-- Definition 14.1: the auxiliary state x^{k,i} uses the new iterate. -/\n'
                  'def alternating_minimization_auxiliary_iterate (x : Nat) := x\n'
                  '/-- The state at zero agrees with the outer iterate. -/\n'
                  '@[simp] theorem alternating_minimization_auxiliary_iterate_zero (x : Nat) :\n'
                  '  alternating_minimization_auxiliary_iterate x = x := by rfl\n')
        excerpts = statement_excerpts(source, label='Definition 14.1')
        self.assertEqual(excerpts[0].signature,
                         'def alternating_minimization_auxiliary_iterate (x : Nat) := x')

    def test_nesterov_auxiliary_objective_headings_keep_source_order(self):
        # Regression: Nesterov Chap02/Lemma_2_21 has two legitimate numbered
        # sides. Neither "auxiliary" nor "helper" in body prose is a marker.
        source = ('/-- The bound follows from Lemma 2.21. -/\nlemma citation : True := by trivial\n'
                  '/-- Auxiliary bridge for Lemma 2.21. -/\nlemma bridge : True := by trivial\n'
                  '/-- Lemma 2.21 (below-threshold side): the auxiliary objective attains its minimum. '
                  'A helper establishes the bound. -/\n'
                  'theorem constrainedAuxiliaryOptimalValue_pos_of_lt : True := by trivial\n'
                  '/-- Lemma 2.21 (above-threshold side): the value is nonpositive. -/\n'
                  'theorem constrainedAuxiliaryOptimalValue_nonpos_of_le : True := by trivial\n')
        excerpts = statement_excerpts(source, label='Lemma 2.21')
        self.assertEqual([item.signature for item in excerpts[:2]], [
            'theorem constrainedAuxiliaryOptimalValue_pos_of_lt : True',
            'theorem constrainedAuxiliaryOptimalValue_nonpos_of_le : True',
        ])
        self.assertEqual(excerpts[-1].signature, 'lemma bridge : True')

    def test_auxiliary_in_body_does_not_change_unlabelled_fallback_order(self):
        source = ('/-- An auxiliary objective on the state space. -/\ndef first := 1\n'
                  '/-- Another definition. -/\ndef second := 2\n'
                  '/-- Auxiliary bridge. -/\ndef bridge := 3\n')
        self.assertEqual([item.signature for item in statement_excerpts(source, label='Definition 9.9')],
                         ['def first := 1', 'def second := 2', 'def bridge := 3'])

    def test_label_boundaries_and_unlabelled_fallback_are_stable(self):
        source = ('/-- Lemma 1.2.30 -/\nlemma wrong : True := by trivial\n'
                  '/-- Helper for Lemma 1.2.3 -/\nlemma helper : True := by trivial\n'
                  '/-- Lemma 1.2.3.1 -/\nlemma nested : True := by trivial\n'
                  '/-- Lemma 1-2-3. The result. -/\nlemma actual : True := by trivial\n')
        self.assertEqual(statement_excerpts(source, label='Lemma 1.2.3')[0].signature,
                         'lemma actual : True')
        self.assertEqual(statement_excerpts(source, label='Lemma 9.9')[0].signature,
                         'lemma wrong : True')

    def test_structures_classes_and_inductives_keep_their_mathematical_bodies(self):
        definitions = [
            'structure Witness where\n  value : Nat\n  positive : 0 < value',
            'class Condition (n : Nat) : Prop where\n  positive : 0 < n\n  default : Nat := 1',
            'inductive Generator\n  | a\n  | b\n  deriving DecidableEq',
            'inductive Relation : Nat → Prop where\n  | zero : Relation 0\n  | next (n) : Relation n → Relation (n+1)',
        ]
        source = '\n\n'.join(definitions) + '\nlemma later : True := by trivial\n'
        excerpts = statement_excerpts(source)
        self.assertEqual([item.signature for item in excerpts[:-1]], definitions)
        self.assertEqual(excerpts[-1].signature, 'lemma later : True')

    def test_statement_excerpts_omit_proofs_and_prefer_numbered_statement(self):
        source = ('import Mathlib\nnamespace Test\nvariable (n : Nat)\n'
                  '@[simp]\nprivate theorem helper : True := by trivial\n'
                  '/-- Lemma 1.2.3: zero is a lower bound. -/\n'
                  'theorem bound (a : Nat := 0) : 0 ≤ n := by\n  exact Nat.zero_le _\n'
                  'end Test\n#check Nat\n')
        excerpts = statement_excerpts(source, label='Lemma 1.2.3')
        self.assertEqual(len(excerpts), 2)
        self.assertEqual(excerpts[0].signature, 'theorem bound (a : Nat := 0) : 0 ≤ n')
        self.assertEqual(excerpts[0].context, ('namespace Test', 'variable (n : Nat)'))
        self.assertEqual(excerpts[1].context, ())
        self.assertNotIn('exact', repr(excerpts))

    def test_literal_contents_do_not_invent_commands_or_end_signatures(self):
        source = ('def text := r#"text "quoted"\n#check fake\n"#\n'
                  "def brace := '('\nrecall actual (n : Nat) : n = n\n")
        excerpts = statement_excerpts(source)
        self.assertEqual(len(excerpts), 3)
        self.assertIn('"quoted"', excerpts[0].signature)
        self.assertEqual(excerpts[1].signature, "def brace := '('")
        self.assertEqual(excerpts[2].signature, 'recall actual (n : Nat) : n = n')

    def test_indented_namespaces_and_multiline_checks(self):
        excerpts = statement_excerpts('namespace X\n  variable (n : Nat)\n'
                                      '  #check\n    (n, n)\nend X\n')
        self.assertEqual(len(excerpts), 1)
        self.assertEqual(excerpts[0].signature, '#check\n    (n, n)')
        self.assertEqual(excerpts[0].context, ('namespace X', 'variable (n : Nat)'))

    def test_assignments_and_matches_inside_a_type_are_not_proof_boundaries(self):
        excerpts = statement_excerpts('theorem foo : let n := 0; n = n := by rfl\n'
                                      'theorem bar : match true with\n | true => True\n | false => False\n := by trivial\n')
        self.assertEqual(excerpts[0].signature, 'theorem foo : let n := 0; n = n')
        self.assertIn('| false => False', excerpts[1].signature)
        self.assertNotIn('trivial', excerpts[1].signature)

    def test_extra_command_indentation_and_local_instances_do_not_swallow_statements(self):
        excerpts = statement_excerpts('variable (n : Nat)\n'
                                      '  theorem bound : 0 ≤ n := by\n  exact Nat.zero_le _\n'
                                      'local instance : Inhabited Nat := by exact ⟨0⟩\n'
                                      '#check Nat\n')
        self.assertEqual(len(excerpts), 3)
        self.assertEqual(excerpts[0].signature, 'theorem bound : 0 ≤ n')
        self.assertNotIn('exact', repr(excerpts))
        self.assertEqual(excerpts[-1].context, ('variable (n : Nat)',))

    def test_mixed_recall_page_does_not_repeat_proofs_or_existing_declarations(self):
        with tempfile.TemporaryDirectory() as temp:
            source = ('import Mathlib\nrecall imported : True\n'
                      'theorem local_result : True := by\n  trivial\n')
            original = '<div class="decl" id="local_result">local_result : True</div>'
            args = self.fixture(Path(temp), {'Demo.Item': source}, contents={'Demo.Item': original})
            enrich_documentation(*args)
            page = (args[0] / 'Demo/Item.html').read_text()
            self.assertIn('recall imported : True', page)
            self.assertEqual(page.count('local_result : True'), 1)
            self.assertNotIn('trivial', page)

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
        self.assertTrue(source_reading('module\npublic import A\npublic section\n'
                                      'open X\nuniverse u\nvariable {a : Type u}\nend\n').imports_only)
        self.assertFalse(source_reading('import A\nopen X in theorem foo : True := trivial\n').imports_only)
        self.assertFalse(source_reading('import A\ncustom_command foo\n').imports_only)

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

    def test_contents_sort_item_numbers_before_statement_kinds(self):
        with tempfile.TemporaryDirectory() as temp:
            items = ['Demo.Chap02.Construction_2_1', 'Demo.Chap01.Theorem_1_1_10',
                     'Demo.Chap01.Construction_1_1_2', 'Demo.Chap01.Definition_1_1_1']
            args = self.fixture(Path(temp), {'Demo.Book': '\n'.join('import ' + item for item in items),
                                           **{item: '#check Nat' for item in items}})
            enrich_documentation(*args)
            page = (args[0] / 'Demo/Book.html').read_text()
            offsets = [page.index(item.replace('Demo.', '').replace('.', '/') + '.html')
                       for item in reversed(items)]
            self.assertEqual(offsets, sorted(offsets))
            self.assertEqual(page.count('<h3>Chapter 1</h3>'), 1)

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
