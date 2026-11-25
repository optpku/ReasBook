"""Audit the paper-proof edges separately from kernel-extracted dependencies."""
import json
from pathlib import Path
import unittest

from generate_latest_graph import RESULTS, PAPER_DEPENDENCY_EVIDENCE


class LatestGraphTests(unittest.TestCase):
    def test_reviewed_paper_dependencies(self):
        # Independent manuscript review: shared theorem counter, November 17 draft.
        expected = {1: [], 2: [], 3: [1, 2], 4: [1], 5: [2, 4],
                    6: [4, 5], 7: [6], 8: [2, 5, 7], 9: [8],
                    10: [3, 5, 7, 8, 9], 11: [10], 12: [], 13: [12]}
        numbers = {row[0]: i for i, row in enumerate(RESULTS, 1)}
        root = Path(__file__).resolve().parents[1] / 'theorem-map/latest'
        for name in ('data.json', 'overview-data.json'):
            data = json.loads((root / name).read_text())
            self.assertEqual(len(data['items']), 13)
            actual = {numbers[item['id']]: [numbers[d] for d in item['dependencies']]
                      for item in data['items']}
            self.assertEqual(actual, expected)
            edges = {(d, item['id']) for item in data['items'] for d in item['dependencies']}
            self.assertEqual(len(edges), 19)
            self.assertEqual({(w['source'], w['target']) for w in data['edgeWitnesses']}, edges)
            self.assertNotIn('compiledItemCount', data['generation'])
            for item in data['items']:
                self.assertEqual(item['dependencyEvidence'], 'curated')
                self.assertEqual(item['statementDependencies'], [])
                self.assertEqual(item['proofDependencies'], [])
            for source, target in edges:
                self.assertLess(numbers[source], numbers[target], 'Not a DAG in source order')
                lines, reason = PAPER_DEPENDENCY_EVIDENCE[target][source]
                self.assertLessEqual(lines[0], lines[1])
                self.assertTrue(reason)


if __name__ == '__main__':
    unittest.main()
