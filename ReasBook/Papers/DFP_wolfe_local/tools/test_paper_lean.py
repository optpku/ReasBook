"""Check declaration source ranges and coverage of the code panel."""
import hashlib
import json
from pathlib import Path
import unittest

from extract_paper_lean import excerpt


class LeanExcerptTests(unittest.TestCase):
    def test_unicode_columns_and_complete_multiline_proof(self):
        source = '/-- Doc. -/\ntheorem sample (α : ℝ) : α = α := by\n  rfl\n\ntheorem next : True := trivial\n'
        self.assertEqual(excerpt(source, 2, 3, 5),
                         'theorem sample (α : ℝ) : α = α := by\n  rfl')
        self.assertEqual(excerpt('αβγ\n', 1, 1, 2), 'αβ')
        with self.assertRaises(ValueError):
            excerpt(source, 2, 3, 100)

    def test_all_mapped_declarations_have_exact_source_code(self):
        root = Path(__file__).resolve().parents[1]
        graph = json.loads((root / 'theorem-map/paper-data.json').read_text())
        data = json.loads((root / 'theorem-map/paper-lean.json').read_text())
        expected = {row['declaration'] for item in graph['items'] for row in item['relatedDeclarations']}
        self.assertEqual(set(data['declarations']), expected)
        self.assertEqual(len(expected), 32)
        self.assertEqual(data['sourceCommit'], graph['project']['commit'])
        for name, row in data['declarations'].items():
            source = (root / row['file']).read_bytes()
            self.assertEqual(hashlib.sha256(source).hexdigest(), row['sourceSha256'])
            exact = excerpt(source.decode(), row['startLine'], row['endLine'], row['endColumn'])
            self.assertEqual(row['code'], exact, name)
            self.assertEqual(hashlib.sha256(exact.encode()).hexdigest(), row['codeSha256'])
            self.assertIn(name.split('.')[-1], exact.splitlines()[0])
            self.assertIn(':=', exact)


if __name__ == '__main__':
    unittest.main()
