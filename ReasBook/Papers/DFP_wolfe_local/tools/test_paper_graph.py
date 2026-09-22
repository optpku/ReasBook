"""Checks for proof-component contraction and the checked-in paper projection."""
import json
from pathlib import Path
import unittest

from generate_paper_graph import project_graph, verify


def declaration(name, statement=(), proof=()):
    return dict(id=name, declaration=name, label=name, title=name, file='Example.lean',
                line=1, type='Theorem', section='main', statement='',
                statementDependencies=list(statement), proofDependencies=list(proof),
                dependencies=sorted(set(statement) | set(proof)), dependencyEvidence='compiled')


def result(name, declarations):
    return dict(id=name, label=name, title=name, section='main', summary=name,
                mapping='Test grouping', texLabel=name, declarations=declarations)


class PaperGraphTests(unittest.TestCase):
    def test_contract_helpers_and_retain_origin_class(self):
        graph = dict(project={}, generation={'compiledItemCount': 5}, items=[
            declaration('a', statement=['helper'], proof=['a_support']),
            declaration('helper', proof=['b']), declaration('b'),
            declaration('a_support', proof=['c']), declaration('c')])
        mapping = dict(manuscript='fixture', numbering='fixture', items=[
            result('A', ['a', 'a_support']), result('B', ['b']), result('C', ['c'])])
        projected = project_graph(graph, mapping)
        a = projected['items'][0]
        self.assertEqual(a['statementDependencies'], ['B'])
        self.assertEqual(a['proofDependencies'], ['C'])
        self.assertEqual(a['dependencies'], ['B', 'C'])
        verify(graph, projected)

    def test_source_only_cannot_masquerade_as_compiled_mapping(self):
        row = declaration('a')
        row['dependencyEvidence'] = 'source-only'
        with self.assertRaisesRegex(ValueError, 'Missing compiled'):
            project_graph(dict(items=[row]), dict(items=[result('A', ['a'])]))

    def test_checked_in_projection_matches_original_graph(self):
        root = Path(__file__).resolve().parents[1]
        graph = json.loads((root / 'theorem-map/data.json').read_text())
        mapping = json.loads((root / 'tools/paper_results.json').read_text())
        published = json.loads((root / 'theorem-map/paper-data.json').read_text())
        rebuilt = project_graph(graph, mapping)
        self.assertEqual(published['items'], rebuilt['items'])
        self.assertEqual(published['edgeWitnesses'], rebuilt['edgeWitnesses'])
        self.assertEqual(len(published['items']), 11)
        self.assertEqual(sum(len(x['dependencies']) for x in published['items']), 22)
        verify(graph, published)
        visiting, visited = set(), set()
        items = {x['id']: x for x in published['items']}
        def walk(node):
            self.assertNotIn(node, visiting, 'Circular grouped dependency')
            if node in visited:
                return
            visiting.add(node)
            for dependency in items[node]['dependencies']:
                walk(dependency)
            visiting.remove(node)
            visited.add(node)
        for item in items:
            walk(item)


if __name__ == '__main__':
    unittest.main()
