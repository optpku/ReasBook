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
        self.assertIn('public import DFPWolfe.V21\n', root)
        routes = json.loads((self.paper / 'tools/verso_modules.json').read_text())['modules']
        self.assertEqual([row['slug'] for row in routes[:8]], [
            'main-theorems', 'global-convergence', 'level-set-convergence',
            'holder-regularity', 'holder-sharpness', 'secant-degeneration',
            'planar-convergence', 'hessian-holder'])
        self.assertEqual(len(routes), 11)
        self.assertTrue(all(row['slug'].startswith('v21-') for row in routes[8:]))
        self.assertNotEqual(self.graph['project']['commit'],
            json.loads((self.paper / 'theorem-map/data.json').read_text())['project']['commit'])

    def test_every_graph_node_has_compiled_evidence_and_matching_source(self):
        items = self.graph['items']
        self.assertGreater(len(items), 50)
        self.assertEqual(len(items), self.graph['generation']['compiledItemCount'])
        self.assertEqual(self.graph['generation']['sourceOnlyItemCount'], 0)
        self.assertIn('full v21 counterexample not yet proved', self.graph['generation']['scope'])
        names = {item['id'] for item in items}
        commit = self.graph['project']['commit']
        checked_files = set()
        for item in items:
            self.assertEqual(item['dependencyEvidence'], 'compiled')
            self.assertTrue(item['declaration'].startswith('DFP.Polar.'))
            source = self.paper / item['file']
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), item['sourceSha256'])
            lines = source.read_text().splitlines(keepends=True)
            start = item['line'] - 1
            self.assertTrue(''.join(lines[start:]).startswith(item['leanCode']))
            self.assertTrue(item['leanCode'].lstrip().startswith(('theorem ', 'lemma ')))
            self.assertEqual(set(item['dependencies']),
                set(item['statementDependencies']) | set(item['proofDependencies']))
            self.assertTrue(set(item['dependencies']) <= names)
            self.assertNotIn(item['id'], item['dependencies'])
            if item['file'] not in checked_files:
                relative = source.relative_to(self.repo).as_posix()
                pinned = subprocess.check_output(['git', 'show', f'{commit}:{relative}'], cwd=self.repo)
                self.assertEqual(pinned, source.read_bytes())
                checked_files.add(item['file'])

    def test_source_overview_edges_have_compiled_witnesses(self):
        self.assertEqual(len(self.overview['items']), 3)
        self.assertEqual([row['label'] for row in self.overview['items']],
            ['Section 3.1', 'Section 3.2', 'Two-cycle equation'])
        verify(self.graph, self.overview)
        self.assertTrue(self.overview['edgeWitnesses'])
        for row in self.overview['items']:
            self.assertTrue(row['relatedDeclarations'])
            self.assertTrue(row['leanCode'])


if __name__ == '__main__':
    unittest.main()
