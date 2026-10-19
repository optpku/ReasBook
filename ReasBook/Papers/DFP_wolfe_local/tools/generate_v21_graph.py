#!/usr/bin/env python3
"""Build a separate compiled graph for the v21 polar foundations.

The SDK contracts private helpers and definitions. Edges are extracted from
Lean types and proof terms, never inferred from manuscript prose. The earlier
center-manifold graph is left intact. Use Python 3.11 or newer.
"""
from __future__ import annotations

import argparse
from bisect import bisect_left
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from generate_theorem_map import mask_comments
from generate_paper_graph import project_graph, verify


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--reuse-evidence', type=Path, help='Reuse checksum-verified export for identical committed sources')
    args = parser.parse_args()
    paper = Path(__file__).resolve().parents[1]
    repo = paper.parents[2]
    sdk = args.sdk_root.resolve()
    output, evidence = args.output.resolve(), args.evidence.resolve()
    if output.exists() or evidence.exists():
        parser.error('output and evidence must be new directories')
    if repo == evidence or repo in evidence.parents:
        parser.error('keep evidence outside the source repository')
    files = sorted((paper / 'ReasLib/Optimization/DFP/Polar').rglob('*.lean'))
    files += sorted((paper / 'DFPWolfe/V21').rglob('*.lean'))
    files += [paper / 'DFPWolfe/V21.lean']
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    for path in files:
        relative = path.relative_to(repo).as_posix()
        committed = subprocess.check_output(['git', 'show', f'{commit}:{relative}'], cwd=repo)
        if committed != path.read_bytes():
            raise RuntimeError('Commit the Lean source before extraction: ' + relative)
    sys.path[:0] = [str(sdk / 'src'), str(sdk.parent / 'common/src')]
    from theorem_graph_sdk.analysis import DECL_RE, PALETTE, contract_dependencies
    from theorem_graph_sdk.extractor import LeanEnvironmentExtractor
    from theorem_graph_sdk.models import Project
    from theorem_graph_sdk.render import copy_generic_map

    original = sdk / 'src/theorem_graph_sdk/resources/Extract.lean'
    text = original.read_text()
    predicate = 'moduleName.toString.splitOn "." |>.contains projectId'
    if text.count(predicate) != 1:
        raise RuntimeError('Review changed SDK ownership predicate before regenerating')
    text = text.replace(predicate,
        'moduleName.toString.startsWith "ReasLib.Optimization.DFP.Polar." ||\n'
        '  moduleName.toString.startsWith "DFPWolfe.V21"')
    # Retain compiler declaration ranges for exact source excerpts below each statement.
    text = text.replace('  line : Nat\n', '  line : Nat\n  endLine : Nat\n  endColumn : Nat\n', 1)
    text = text.replace('    line\n    kind :=',
        '    line\n    endLine := ranges?.map (·.range.endPos.line) |>.getD line\n'
        '    endColumn := ranges?.map (·.range.endPos.column) |>.getD 0\n    kind :=', 1)
    evidence.mkdir(parents=True)

    def bounded_runner(command, **kwargs):
        command = list(command)
        config_path = Path(command[-2])
        config = json.loads(config_path.read_text())
        for spec in config['projects']:
            spec.setdefault('rootModules', [])
        config_path.write_text(json.dumps(config))
        i = command.index('lean') + 1
        command[i:i] = ['-j1', '-M8192']
        result = subprocess.run(command, **kwargs)
        (evidence / 'extraction.log').write_text(result.stdout + result.stderr)
        return result

    project = Project('papers', 'Papers', 'Paper', 'DFP_wolfe_local', paper, 'DFPWolfe.V21')
    if args.reuse_evidence:
        saved_root = args.reuse_evidence.resolve()
        saved = json.loads((saved_root / 'provenance.json').read_text())
        source_identity = [dict(file=path.relative_to(paper).as_posix(), sha256=digest(path))
                           for path in files]
        if (saved['sourceCommit'] != commit or saved['sources'] != source_identity or
                saved['extractorSha256'] != digest(original) or
                saved['rawSha256'] != digest(saved_root / 'raw.json')):
            raise RuntimeError('Cached export source, extractor or checksum mismatch')
        raw = json.loads((saved_root / 'raw.json').read_text())
    else:
        with tempfile.TemporaryDirectory(prefix='dfp-v21-extract-') as temporary:
            extractor = Path(temporary) / 'Extract.lean'
            extractor.write_text(text)
            raw = LeanEnvironmentExtractor(extractor, runner=bounded_runner,
                timeout_seconds=1800).extract_project(repo, project)[project.project_id]
    (evidence / 'raw.json').write_text(json.dumps(raw, ensure_ascii=False))
    heads = {}
    pattern = re.compile(r'^[ \t]*(?:@\[[\s\S]*?\]\s*)*'
        r'(?P<modifiers>(?:(?:private|protected|public|noncomputable)\s+)*)'
        r'(?P<kind>theorem|lemma)\s+(?P<name>[^\s({:\[=]+)', re.MULTILINE)
    sources = []
    for path in files:
        source = path.read_text()
        docs = {m.start('name'): m['doc'].strip() for m in DECL_RE.finditer(source)}
        records = []
        for m in pattern.finditer(mask_comments(source)):
            records.append(dict(name=m['name'].strip('«»'),
                line=source.count('\n', 0, m.start('kind')) + 1,
                private='private' in m['modifiers'], doc=docs.get(m.start('name'), '')))
        heads[path.relative_to(paper).as_posix()] = records
        sources.append(dict(file=path.relative_to(paper).as_posix(), sha256=digest(path)))
    selected = []
    for item in raw:
        if item['kind'] != 'theorem' or item['name'].startswith('_private.'):
            continue
        file = item['moduleName'].replace('.', '/') + '.lean'
        records = heads.get(file, [])
        i = bisect_left([r['line'] for r in records], item['line'])
        if i == len(records):
            continue
        head = records[i]
        if head['private'] or not (item['name'] == head['name'] or
                item['name'].endswith('.' + head['name'])):
            continue
        selected.append({**item, 'file': file, 'line': head['line']})
    expected = sum(not r['private'] for records in heads.values() for r in records)
    if len(selected) != expected:
        raise RuntimeError(f'Compiled graph coverage mismatch: {len(selected)} / {expected}')
    raw_by_name = {item['name']: item for item in raw}
    chosen = {item['name']: item['name'] for item in selected}
    sections, section_ids, items = [], {}, []
    for item in sorted(selected, key=lambda row: (row['file'], row['line'])):
        group = Path(item['file']).stem
        if group not in section_ids:
            key = 'section-' + str(len(sections))
            section_ids[group] = key
            color, wash = PALETTE[len(sections) % len(PALETTE)]
            sections.append(dict(id=key, label=group, short=group, color=color, wash=wash))
        dependencies = {field: sorted(set(contract_dependencies(
            item['name'], raw_by_name, chosen, field)) - {item['name']})
            for field in ('statementDependencies', 'proofDependencies', 'dependencies')}
        if set(dependencies['dependencies']) != (set(dependencies['statementDependencies']) |
                set(dependencies['proofDependencies'])):
            raise RuntimeError('Statement/proof dependency union mismatch')
        label = item['name'].removeprefix('DFP.Polar.')
        source = (paper / item['file']).read_text()
        lines = source.splitlines(keepends=True)
        begin, end, column = item['line'], item['endLine'], item['endColumn']
        if not 1 <= begin <= end <= len(lines):
            raise RuntimeError('Invalid compiler declaration range: ' + item['name'])
        code = ''.join(lines[begin - 1:end - 1]) + lines[end - 1][:column]
        if not re.match(r'\s*(?:theorem|lemma)\s+', code):
            raise RuntimeError('Source excerpt does not begin at a declaration')
        items.append(dict(id=item['name'], label=label, title=label, type='Theorem',
            section=section_ids[group], file=item['file'], line=item['line'],
            declaration=item['name'], statement=item['docString'],
            dependencyEvidence='compiled', leanCode=code, endLine=end,
            sourceSha256=digest(paper / item['file']), **dependencies))
    source_hash = hashlib.sha256(json.dumps(sources, sort_keys=True).encode()).hexdigest()
    data = dict(schemaVersion=2, project=dict(id=project.project_id,
        title='DFP v21: polar foundations (partial proof)', kind='papers', branch='v4.32.0',
        commit=commit, repository='https://github.com/optpku/ReasBook',
        sourceRoot=project.source_root), sections=sections, items=items,
        generation=dict(mode='lean-environment', rootModule=project.root_module,
            compiledItemCount=len(items), sourceInventoryItemCount=expected,
            sourceOnlyItemCount=0, mergedItemCount=len(items), dependencyCoverage='complete',
            dependencyModel='statement-and-proof-v1', sourceSha256=source_hash,
            extractorSha256=digest(original), scope='v21 polar foundations only; full v21 counterexample not yet proved',
            sourceSnapshot='c788aa3dabd6cac78f4ec8b2c9c1e897cbc1188f'))
    copy_generic_map(sdk / 'src/theorem_graph_sdk/resources/assets', output, data)
    bundles = [
        dict(id='v21-polar-data', label='Section 3.1', title='Prescribed polar data',
            section='construction', texLabel='eq:polar-matrix-map',
            mapping='Definitions and exact recurrence identities only; radius-product convergence is not asserted.',
            declarations=[item['declaration'] for item in items if '/Normalized/' not in item['file']
                and not item['file'].endswith('/TwoCycle.lean')]),
        dict(id='v21-normalized-map', label='Section 3.2', title='Normalized map and regularity',
            section='construction', texLabel='eq:polar-leading-map',
            mapping='Exact normalized recurrence, analytic canceled map and compact-uniform Taylor interface. Restoring drift and the invariant tube are not asserted.',
            declarations=[item['declaration'] for item in items if '/Normalized/' in item['file']]),
        dict(id='v21-two-cycle', label='Two-cycle equation', title='Limiting two-cycle family',
            section='construction', texLabel='eq:polar-two-cycle',
            mapping='The rational limiting two-cycle, its local inverse and reference data; this does not prove continuation of the perturbed orbit.',
            declarations=[item['declaration'] for item in items if item['file'].endswith('/TwoCycle.lean')]),
    ]
    overview = project_graph(data, dict(items=bundles, manuscript='October 9, 2026 v21 submission',
        numbering='Source section/equation locators, not newly completed numbered theorems.'))
    verify(data, overview)
    by_name = {item['declaration']: item for item in items}
    samples = [
        ['DFP.Polar.Parameters.matrix_succ'],
        ['DFP.Polar.Parameters.normalizedEvenState_succ', 'DFP.Polar.Normalized.map_uniformJets'],
        ['DFP.Polar.TwoCycle.evenToOdd', 'DFP.Polar.TwoCycle.oddToEven'],
    ]
    for item, bundle, names in zip(overview['items'], bundles, samples):
        item['statement'] = bundle['mapping']
        primary = by_name[names[0]]
        item.update({key: primary[key] for key in ('declaration', 'file', 'line', 'endLine')})
        item['leanCode'] = primary['leanCode']
        item['leanExcerpts'] = [{key: by_name[name][key] for key in
            ('declaration', 'file', 'line', 'leanCode')} for name in names]
        item['type'] = 'Equation' if item['id'] == 'v21-two-cycle' else 'Section'
    (output / 'overview-data.json').write_text(json.dumps(overview, indent=2, ensure_ascii=False) + '\n')
    # Only the v21 viewer gains a source panel; the original map is preserved.
    app = output / 'app.js'
    javascript = app.read_text()
    marker = '    var relationSection = document.createElement("section");'
    panel = '''    if (item.leanCode) {
      var codeHeading = document.createElement("h3");
      codeHeading.textContent = "Corresponding Lean code";
      statementSection.appendChild(codeHeading);
      (item.leanExcerpts || [item]).forEach(function (excerpt) {
        var sourceLink = document.createElement("a");
        sourceLink.className = "detail-source-link";
        sourceLink.textContent = excerpt.declaration;
        sourceLink.href = sourceUrl(excerpt);
        sourceLink.target = "_blank";
        sourceLink.rel = "noreferrer";
        var code = document.createElement("pre");
        code.className = "v21-lean-code";
        code.textContent = excerpt.leanCode;
        statementSection.appendChild(sourceLink);
        statementSection.appendChild(code);
      });
    }

'''
    if javascript.count(marker) != 1:
        raise RuntimeError('Review changed SDK detail renderer before regenerating')
    javascript = javascript.replace(marker, panel + marker)
    javascript = javascript.replace('fetch("./data.json",',
        'fetch(new URLSearchParams(window.location.search).get("view") === "lean" ? "./data.json" : "./overview-data.json",')
    javascript = javascript.replace('statementHeading.textContent = "Natural-language statement";',
        'statementHeading.textContent = item.paperMapping ? "Source correspondence and scope" : "Declaration description";')
    app.write_text(javascript)
    css = output / 'styles.css'
    css.write_text(css.read_text() + '\n.v21-lean-code { white-space: pre; overflow-x: auto; '
        'max-width: 100%; padding: 1rem; background: #f6f8fa; border-radius: 6px; '
        'font-family: ui-monospace, monospace; }\n.detail-scroll { grid-column: 2; }\n'
        '.version-links { padding: .5rem 1rem; background: #f6f8fa; }\n')
    index = output / 'index.html'
    index.write_text(index.read_text().replace('<body>', '<body>\n<nav class="version-links">'
        '<a href="../index.html?view=paper">Original center-manifold proof</a> · '
        '<strong>v21 polar foundations — partial proof</strong> · '
        '<a href="?view=paper">Source sections</a> · <a href="?view=lean">Lean declarations</a></nav>', 1))
    (evidence / 'provenance.json').write_text(json.dumps(dict(sourceCommit=commit,
        sources=sources, sourceSha256=source_hash, extractorSha256=digest(original),
        rawSha256=digest(evidence / 'raw.json')), indent=2) + '\n')
    print(json.dumps(dict(output=str(output), nodes=len(items),
        edges=sum(len(item['dependencies']) for item in items), sourceCommit=commit), indent=2))


if __name__ == '__main__':
    main()
