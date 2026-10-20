"""Check separation of proof versions and the compiled v21 graph's evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
import unittest

from generate_paper_graph import verify


class V21ResourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.paper = Path(__file__).resolve().parents[1]
        cls.repo = cls.paper.parents[2]
        cls.graph = json.loads((cls.paper / 'theorem-map/v21/data.json').read_text())
        cls.overview = json.loads((cls.paper / 'theorem-map/v21/overview-data.json').read_text())

    def test_v21_entry_and_reading_routes_preserve_original_version(self):
        root = (self.paper / 'Paper.lean').read_text()
        self.assertIn('public import DFPWolfe\n', root)
        self.assertIn('public import DFPWolfe.V21.Paper\n', root)
        routes = json.loads((self.paper / 'tools/verso_modules.json').read_text())['modules']
        self.assertEqual([row['slug'] for row in routes[:8]], [
            'main-theorems', 'global-convergence', 'level-set-convergence',
            'holder-regularity', 'holder-sharpness', 'secant-degeneration',
            'planar-convergence', 'hessian-holder'])
        self.assertEqual(len(routes), 21)
        self.assertTrue(all(row['slug'].startswith('v21-') for row in routes[8:]))
        self.assertNotEqual(self.graph['project']['commit'],
            json.loads((self.paper / 'theorem-map/data.json').read_text())['project']['commit'])

    def test_every_graph_node_has_compiled_evidence_and_matching_source(self):
        items = self.graph['items']
        self.assertGreater(len(items), 50)
        self.assertEqual(len(items), self.graph['generation']['compiledItemCount'])
        self.assertEqual(self.graph['generation']['sourceOnlyItemCount'], 0)
        self.assertIn('Complete v21 numbered results 1–8', self.graph['generation']['scope'])
        names = {item['id'] for item in items}
        commit = self.graph['project']['commit']
        checked_files = set()
        for item in items:
            self.assertEqual(item['dependencyEvidence'], 'compiled')
            self.assertTrue(item['file'].startswith(('DFPWolfe/', 'ReasLib/')))
            source = self.paper / item['file']
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), item['sourceSha256'])
            lines = source.read_text().splitlines(keepends=True)
            start = item['line'] - 1
            self.assertIn(item['leanCode'], ''.join(lines[start:item['endLine']]))
            self.assertRegex(item['leanCode'].lstrip(), r'^(?:theorem|lemma)\s')
            self.assertEqual(set(item['dependencies']),
                set(item['statementDependencies']) | set(item['proofDependencies']))
            self.assertTrue(set(item['dependencies']) <= names)
            self.assertNotIn(item['id'], item['dependencies'])
            if item['file'] not in checked_files:
                relative = source.relative_to(self.repo).as_posix()
                pinned = subprocess.check_output(['git', 'show', f'{commit}:{relative}'], cwd=self.repo)
                self.assertEqual(pinned, source.read_bytes())
                checked_files.add(item['file'])

    def test_exact_statement_inventory_and_scope(self):
        statements = json.loads((self.paper / 'theorem-map/v21/paper-statements.json').read_text())
        self.assertEqual(statements['manuscriptSha256'],
            '6e6e05b0fae7896b5c944344e28652260d4be010b19616d9058eea5584830188')
        self.assertEqual(len(statements['items']), 8)
        for statement, item in zip(statements['items'], self.overview['items']):
            self.assertEqual(statement['id'], item['id'])
            self.assertEqual(statement['statementLatex'], item['statement'])
            self.assertEqual(hashlib.sha256(item['statement'].encode()).hexdigest(),
                             statement['statementSha256'])
            self.assertEqual(statement['statementHtml'], item['statementHtml'])
            self.assertNotIn('<script', item['statementHtml'])
        by_id = {item['id']: item for item in self.overview['items']}
        self.assertIn('disjoint open balls', by_id['v21-center']['paperMapping'])
        names = {row['declaration'] for row in by_id['v21-main']['relatedDeclarations']}
        self.assertIn('DFPWolfe.V21.planarCounterexampleFamilyWithFullTurn', names)
        self.assertIn('DFPWolfe.V21.planarCounterexampleFamilyWithSequenceProperties', names)
        self.assertIn('v21-main', {item['id'] for item in self.overview['items']})

    def test_source_overview_edges_have_compiled_witnesses(self):
        self.assertEqual(len(self.overview['items']), 8)
        self.assertEqual([row['label'] for row in self.overview['items']],
            ['Theorem 1', 'Corollary 2', 'Theorem 3', 'Lemma 4', 'Lemma 5', 'Lemma 6', 'Lemma 7', 'Proposition 8'])
        verify(self.graph, self.overview)
        self.assertTrue(self.overview['edgeWitnesses'])
        by_id = {row['id']: row for row in self.overview['items']}
        self.assertEqual(by_id['v21-identity']['dependencies'], ['v21-main'])
        self.assertIn('v21-degeneration', by_id['v21-convergence']['dependencies'])
        for row in self.overview['items']:
            self.assertTrue(row['relatedDeclarations'])
            self.assertTrue(row['leanCode'])
            primary = row['leanExcerpts'][0]
            self.assertEqual(row['file'], primary['file'])
            self.assertEqual(row['line'], primary['line'])
            for excerpt in row['leanExcerpts']:
                lines = (self.paper / excerpt['file']).read_text().splitlines(keepends=True)
                self.assertIn(excerpt['leanCode'], ''.join(lines[excerpt['line'] - 1:]))


if __name__ == '__main__':
    unittest.main()
