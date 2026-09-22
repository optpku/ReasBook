"""Guard exact extraction, reference resolution, and statement provenance."""
import hashlib
import json
from pathlib import Path
import unittest

from extract_paper_statements import display_latex, extract
from generate_paper_graph import attach_statements, project_graph


class StatementTests(unittest.TestCase):
    def test_extract_keeps_all_source_text_and_math(self):
        body = r'\label{thm:sample}For every $0<c_1<c_2<1$, either stop or $x_k\to x_*$.'
        manuscript = '\\begin{theorem}[Named result]\n' + body + '\n\\end{theorem}'
        aux = r'\newlabel{thm:sample}{{3}{1}{Title}{theorem.3}{}}'
        mapping = dict(items=[dict(id='sample', texLabel='thm:sample', label='Theorem 3')])
        rows = extract(manuscript, aux, mapping)
        self.assertEqual(rows[0]['statementLatex'], body)
        self.assertEqual(rows[0]['statementSha256'], hashlib.sha256(body.encode()).hexdigest())
        with self.assertRaises(ValueError):
            extract(manuscript, aux.replace('{{3}', '{{4}'), mapping)

    def test_equation_numbers_and_cross_references_are_preserved(self):
        statement = dict(statementLatex=r'See \eqref{eq:a}. \begin{align}x&=1\label{eq:a}\\y&=2\label{eq:b}\end{align}',
                         references={'eq:a': '13'}, equationNumbers={'eq:a': '13', 'eq:b': '14'})
        rendered = display_latex(statement)
        self.assertIn('See (13).', rendered)
        self.assertIn(r'\tag{13}', rendered)
        self.assertIn(r'\tag{14}', rendered)
        self.assertIn('x&=1', rendered)
        self.assertIn('y&=2', rendered)
        self.assertNotIn(r'\label', rendered)

    def test_all_checked_in_excerpts_are_bound_to_nodes(self):
        root = Path(__file__).resolve().parents[1]
        excerpts = json.loads((root / 'theorem-map/paper-statements.json').read_text())
        graph = json.loads((root / 'theorem-map/paper-data.json').read_text())
        original = json.loads((root / 'theorem-map/data.json').read_text())
        mapping = json.loads((root / 'tools/paper_results.json').read_text())
        expected = project_graph(original, mapping)
        attach_statements(expected, excerpts)
        self.assertEqual(graph['items'], expected['items'])
        self.assertEqual(len(excerpts['items']), 11)
        self.assertEqual(sum(x['formulaCount'] for x in excerpts['items']), 113)
        for item in excerpts['items']:
            self.assertEqual(hashlib.sha256(item['statementLatex'].encode()).hexdigest(), item['statementSha256'])
            self.assertNotIn('katex-error', item['statementHtml'])
            self.assertEqual(item['statementHtml'].count('<math '), item['formulaCount'])
            for number in item['equationNumbers'].values():
                self.assertIn(r'\tag{' + number + '}', item['statementHtml'])
        theorem = excerpts['items'][0]['statementLatex']
        self.assertIn('0<c_1<2/3', theorem)
        self.assertIn(r'2/3\le c_2<1', theorem)
        self.assertIn(r'\frac12I\preceq\nabla^2f(x)\preceq\frac32I', theorem)
        self.assertIn('finitely many iterations', excerpts['items'][2]['statementLatex'])


if __name__ == '__main__':
    unittest.main()
