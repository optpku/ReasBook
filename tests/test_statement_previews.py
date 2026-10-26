"""Regression cases for numbered facades with separately owned definitions."""

from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402


class SelectedStatementPreviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.source = Path(self.temp.name) / "ReasBook"
        self.project = self.source / "Papers/TR_LALM_theory"
        self.project.mkdir(parents=True)
        (self.source / 'lakefile.lean').write_text(
            'lean_lib TR_LALM_theory where\n  srcDir := "Papers"\n')
        (self.source / 'lean-toolchain').write_text('leanprover/lean4:v4.32.2\n')
        (self.project / 'Paper.lean').write_text('\n'.join(
            'import TR_LALM_theory.' + stem for stem in
            ('Algorithm_2_1', 'Definition_2_2', 'Definition_3_2', 'Assumption_2_5')) + '\n')
        sources = {
            'Algorithm_2_1': (
                'import TR_LALM_theory.Algorithm_2_1.Iteration\n'
                '/-- Algorithm 2.1 (7): a derived consequence. -/\n'
                'theorem perturbedMultiplierIdentity : True := by trivial\n'),
            'Algorithm_2_1/Model': (
                'def irrelevant := 0\n/-- The quadratic step model. -/\n'
                'def stepModel (x : Nat) := x + 1\n'),
            'Algorithm_2_1/Iteration': (
                'import TR_LALM_theory.Algorithm_2_1.Model\n'
                'def helper := 0\n/-- Generated points and update laws. -/\n'
                'structure Run where\n  point : Nat → Nat\n'
                '  point_succ (k : Nat) : point (k + 1) = point k + 1\n'),
            'Definition_2_2': (
                'import TR_LALM_theory.Definition_2_2.KKT\n'
                '/-- Definition 2.2 (7): a derived residual bound. -/\n'
                'theorem residual_le : True := by trivial\n'),
            'Definition_2_2/KKT': (
                'namespace KKT\ndef helper := 0\n'
                'structure IsApproximatePair (ε : Nat) : Prop where\n'
                '  stationarity_le : 0 ≤ ε\n  feasibility_le : 0 ≤ ε\n'
                'def IsApproximatePoint (ε : Nat) := IsApproximatePair ε\n'
                'def IsPair := IsApproximatePair 0\n'
                'def IsPoint := IsApproximatePoint 0\n'
                'def residual (x : Nat) := x\nend KKT\n'),
            'Definition_3_2': (
                'import TR_LALM_theory.Definition_3_2.Stochastic\n'
                '/-- Definition 3.2 (3): a derived mean-square bound. -/\n'
                'theorem of_residualMeanSquare_le : True := by trivial\n'),
            'Definition_3_2/Stochastic': (
                'namespace KKT.Stochastic\ndef stationarityMeanSquare := 0\n'
                'structure IsApproximatePair : Prop where\n  measurable : True\n'
                'def IsApproximatePoint := IsApproximatePair\nend KKT.Stochastic\n'),
            'Assumption_2_5': 'import TR_LALM_theory.Assumption_2_5.Region\n',
            'Assumption_2_5/Region': (
                'namespace LALM\ndef initialPotentialBound := 1\n'
                'def deterministicObjectiveBound := initialPotentialBound + 1\n'
                'def deterministicSublevel := {x : Nat | x ≤ deterministicObjectiveBound}\n'
                '/-- The required closed-neighborhood containment. -/\n'
                'def DeterministicRegionCondition : Prop := ∀ x ∈ deterministicSublevel, x ≤ 2\n'
                'end LALM\n'),
        }
        for relative, text in sources.items():
            path = self.project / f'{relative}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def render(self, stem):
        item = generator.parse_paper_item(self.project / f'{stem}.lean', self.source)
        self.assertIsNotNone(item)
        return '\n'.join(generator.item_statement_blocks(self.source, item))

    def test_defining_clauses_replace_derived_facade_consequences(self):
        cases = {
            'Algorithm_2_1': ('structure Run', 'point_succ', 'perturbedMultiplierIdentity'),
            'Definition_2_2': ('structure IsApproximatePair', 'feasibility_le', 'residual_le'),
            'Definition_3_2': ('structure IsApproximatePair', 'measurable', 'of_residualMeanSquare_le'),
            'Assumption_2_5': ('def DeterministicRegionCondition', '∀ x ∈ deterministicSublevel', None),
        }
        for stem, (definition, content, wrong) in cases.items():
            with self.subTest(item=stem):
                text = self.render(stem)
                self.assertIn(definition, text)
                self.assertIn(content, text)
                if wrong:
                    self.assertNotIn(wrong, text)
                self.assertIn('not the complete item', text)
                anchor = stem.lower().replace('_', '-')
                self.assertEqual(text.count(f'id := "{anchor}"'), 1)
                ids = re.findall(r'id := "([^"]+)"', text)
                self.assertEqual(len(ids), len(set(ids)))
                self.assertNotIn('by trivial', text)
        condition = self.render('Assumption_2_5')
        self.assertLess(condition.index('def DeterministicRegionCondition'),
                        condition.index('def initialPotentialBound'))

    def test_each_clause_links_its_actual_owner_module(self):
        text = self.render('Algorithm_2_1')
        for owner in ('Model', 'Iteration'):
            self.assertIn(f'docs/ReasBook/TR_LALM_theory/Algorithm_2_1/{owner}.html', text)
            self.assertIn(f'ReasBook/Papers/TR_LALM_theory/Algorithm_2_1/{owner}.lean', text)
        self.assertNotIn('Algorithm_2_1.html', text)
        self.assertIn('namespace KKT', self.render('Definition_2_2'))

    def test_missing_selected_declaration_fails_instead_of_falling_back(self):
        (self.project / 'Algorithm_2_1/Model.lean').write_text('def a_helper := 0\n')
        with self.assertRaisesRegex(ValueError, 'exactly once.*stepModel'):
            self.render('Algorithm_2_1')

    def test_ambiguous_selected_declaration_fails(self):
        (self.project / 'Algorithm_2_1/Model.lean').write_text(
            'namespace A\ndef stepModel := 0\nend A\n'
            'namespace B\ndef stepModel := 1\nend B\n')
        with self.assertRaisesRegex(ValueError, 'exactly once.*stepModel'):
            self.render('Algorithm_2_1')

    def test_missing_owner_module_fails(self):
        with patch.object(generator, 'project_sources', return_value={}):
            with self.assertRaisesRegex(ValueError, 'source is missing'):
                self.render('Algorithm_2_1')

    def test_unreachable_owner_fails_even_if_its_file_still_exists(self):
        (self.project / 'Algorithm_2_1.lean').write_text(
            '/-- Algorithm 2.1 (7): a derived consequence. -/\n'
            'theorem perturbedMultiplierIdentity : True := by trivial\n')
        with self.assertRaisesRegex(ValueError, 'source is not imported'):
            self.render('Algorithm_2_1')

    def test_unmapped_items_keep_numbered_heading_selection(self):
        path = self.project / 'Theorem_9_9.lean'
        path.write_text('/-- Helper for Theorem 9.9. -/\nlemma helper : True := by trivial\n'
                        '/-- Theorem 9.9: an auxiliary objective. -/\ntheorem actual : True := by trivial\n')
        text = self.render('Theorem_9_9')
        self.assertIn('theorem actual : True', text)
        self.assertNotIn('lemma helper', text)

    def test_unpublished_items_keep_statements_and_source_without_dead_doc_links(self):
        (self.project / 'Remark_C_1.lean').write_text(
            '/-- Remark C.1: a historical appendix statement. -/\n'
            'theorem legacy_result : True := by trivial\n'
            'theorem another_result : True := by trivial\n')
        text = self.render('Remark_C_1')
        self.assertIn('theorem legacy_result : True', text)
        self.assertIn('source only (outside the published documentation root)', text)
        self.assertNotIn('Additional statements are available', text)
        self.assertIn('TR_LALM_theory/Remark_C_1.lean', text)
        self.assertNotIn('[Documentation]', text)
        self.assertNotIn('by trivial', text)

    def test_selected_clauses_check_public_root_not_just_facade_imports(self):
        (self.project / 'Paper.lean').write_text('import TR_LALM_theory.Definition_2_2\n')
        text = self.render('Algorithm_2_1')
        self.assertIn('structure Run where', text)
        self.assertEqual(text.count('[Lean source]'), 2)
        self.assertEqual(text.count('outside the published documentation root'), 2)
        self.assertNotIn('[Documentation]', text)

    def test_unpublished_facade_can_link_a_published_owner(self):
        (self.project / 'Algorithm_2_1/Model.lean').write_text('def stepModel := 0\n')
        (self.project / 'Remark_C_1.lean').write_text(
            'import TR_LALM_theory.Algorithm_2_1.Model\n')
        text = self.render('Remark_C_1')
        self.assertIn('def stepModel', text)
        self.assertIn('docs/ReasBook/TR_LALM_theory/Algorithm_2_1/Model.html', text)
        self.assertNotIn('Remark_C_1.html', text)


if __name__ == '__main__':
    unittest.main()
