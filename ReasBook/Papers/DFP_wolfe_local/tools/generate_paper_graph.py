#!/usr/bin/env python3
"""Group the compiled declaration graph by reviewed manuscript result numbers.

Numbers and descriptions come from paper_results.json. Every edge retains a
witness path in the existing compiled graph; no dependencies are inferred from
prose. Multiple supporting Lean declarations may belong to one paper result.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import re


def project_graph(graph, mapping):
    raw = {item['id']: item for item in graph['items']}
    by_declaration = {item['declaration']: item for item in graph['items']
                      if item['dependencyEvidence'] == 'compiled'}
    groups = {}
    for result in mapping['items']:
        for name in result['declarations']:
            if name not in by_declaration:
                raise ValueError(f'Missing compiled declaration: {name}')
            node_id = by_declaration[name]['id']
            if node_id in groups:
                raise ValueError(f'Declaration assigned to two results: {name}')
            groups[node_id] = result['id']

    items, witnesses = [], []
    for result in mapping['items']:
        related = [by_declaration[name] for name in result['declarations']]
        item = {**related[0], 'id': result['id'], 'label': result['label'],
                'title': result['title'], 'type': result['label'].split()[0],
                'section': result['section'], 'statement': '',
                'paperMapping': result['mapping'], 'texLabel': result['texLabel'],
                'relatedDeclarations': [
                    {key: row[key] for key in ('declaration', 'file', 'line')}
                    for row in related]}
        for field in ('statementDependencies', 'proofDependencies'):
            reached = {}
            queue = deque((dependency, [start['id'], dependency])
                          for start in related for dependency in start[field])
            visited = set()
            while queue:
                current, path = queue.popleft()
                if current in visited:
                    continue
                visited.add(current)
                target = groups.get(current)
                if target and target != result['id']:
                    reached.setdefault(target, path)
                    continue
                for dependency in raw[current]['dependencies']:
                    queue.append((dependency, path + [dependency]))
            item[field] = sorted(reached)
            for target, path in sorted(reached.items()):
                witnesses.append(dict(consumer=result['id'], prerequisite=target,
                                      kind=field, declarationPath=path))
        item['dependencies'] = sorted(set(item['statementDependencies']) |
                                      set(item['proofDependencies']))
        items.append(item)
    return dict(schemaVersion=2, project=graph['project'], items=items,
                sections=[
                    dict(id='main', label='Main results', short='Main results', color='#315fb5', wash='#e9effa'),
                    dict(id='construction', label='Counterexample construction', short='Construction', color='#23745d', wash='#e4f2ed'),
                    dict(id='convergence', label='Convergence argument', short='Convergence', color='#7654a6', wash='#eee8f8')],
                generation={**graph['generation'], 'view': 'paper-numbered',
                            'baseGraphItemCount': len(graph['items']),
                            'baseGraphCompiledItemCount': graph['generation']['compiledItemCount'],
                            'compiledItemCount': len(items), 'sourceOnlyItemCount': 0,
                            'sourceInventoryItemCount': len(items), 'mergedItemCount': len(items),
                            'inventoryMode': 'reviewed-paper-components',
                            'dependencyCoverage': 'compiled-component-projection',
                            'selection': 'Reviewed manuscript-result bundles; unassigned nodes are contracted',
                            'dependencyModel': 'compiled-paths-between-paper-components',
                            'paperItemCount': len(items),
                            'mappingScope': 'Nodes identify paper results. Linked declarations include full statements and supporting proof components as described individually.',
                            'numbering': mapping['numbering'],
                            'manuscript': mapping['manuscript']},
                edgeWitnesses=witnesses)


def verify(graph, paper):
    raw = {item['id']: item for item in graph['items']}
    nodes = {item['id']: item for item in paper['items']}
    for witness in paper['edgeWitnesses']:
        path = witness['declarationPath']
        field = witness['kind']
        assert path[1] in raw[path[0]][field]
        for start, end in zip(path[1:], path[2:]):
            assert end in raw[start]['dependencies']
        assert witness['prerequisite'] in nodes[witness['consumer']][field]
        assert raw[path[0]]['declaration'] in {
            x['declaration'] for x in nodes[witness['consumer']]['relatedDeclarations']}
        assert raw[path[-1]]['declaration'] in {
            x['declaration'] for x in nodes[witness['prerequisite']]['relatedDeclarations']}
    for item in paper['items']:
        assert set(item['dependencies']) <= nodes.keys()
        assert item['id'] not in item['dependencies']


def attach_statements(paper, excerpts):
    """Bind full source statements without changing graph relationships."""
    statements = {item['id']: item for item in excerpts['items']}
    if set(statements) != {item['id'] for item in paper['items']}:
        raise ValueError('Statement inventory differs from paper graph')
    for item in paper['items']:
        statement = statements[item['id']]
        if (statement['texLabel'], statement['label']) != (item['texLabel'], item['label']):
            raise ValueError('Statement label mismatch')
        item['statement'] = statement['statementLatex']
        item['statementSha256'] = statement['statementSha256']
        item['statementSource'] = dict(manuscript=excerpts['manuscriptName'],
            manuscriptSha256=excerpts['manuscriptSha256'],
            startLine=statement['sourceStartLine'], endLine=statement['sourceEndLine'])
    paper['generation']['statementMode'] = 'verbatim-manuscript-excerpts'
    paper['generation']['manuscriptSha256'] = excerpts['manuscriptSha256']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph-root', type=Path)
    parser.add_argument('--manuscript', type=Path,
                        help='Optional local TeX file: verify current numbering without publishing it')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    graph_root = args.graph_root or root / 'theorem-map'
    mapping_file = Path(__file__).with_name('paper_results.json')
    mapping = json.loads(mapping_file.read_text())
    graph_bytes = (graph_root / 'data.json').read_bytes()
    graph = json.loads(graph_bytes)
    if args.manuscript:
        text = args.manuscript.read_text()
        blocks = re.findall(r'\\begin\{(theorem|lemma|corollary|proposition)\}([\s\S]*?)\\end\{\1\}', text)
        assert len(blocks) == len(mapping['items'])
        for number, ((kind, body), item) in enumerate(zip(blocks, mapping['items']), 1):
            assert item['label'] == f'{kind.title()} {number}'
            assert '\\label{' + item['texLabel'] + '}' in body
        mapping['manuscriptSha256'] = hashlib.sha256(args.manuscript.read_bytes()).hexdigest()
    result = project_graph(graph, mapping)
    excerpts = json.loads((root / 'theorem-map/paper-statements.json').read_text())
    attach_statements(result, excerpts)
    if args.manuscript and excerpts['manuscriptSha256'] != mapping['manuscriptSha256']:
        raise ValueError('Statements must be re-extracted for this manuscript revision')
    result['generation']['inputGraphSha256'] = hashlib.sha256(graph_bytes).hexdigest()
    result['generation']['mappingSha256'] = hashlib.sha256(mapping_file.read_bytes()).hexdigest()
    if mapping.get('manuscriptSha256'):
        result['generation']['manuscriptSha256'] = mapping['manuscriptSha256']
    verify(graph, result)
    (graph_root / 'paper-data.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(dict(nodes=len(result['items']),
                          edges=sum(len(x['dependencies']) for x in result['items']),
                          typedWitnesses=len(result['edgeWitnesses'])), indent=2))


if __name__ == '__main__':
    main()
