#!/usr/bin/env python3
"""Build a separate compiled graph for the complete v21 proof and its reused infrastructure.

The SDK contracts private helpers and definitions. Edges are extracted from
Lean types and proof terms, never inferred from manuscript prose. The earlier
center-manifold graph is left intact. Use Python 3.11 or newer.
"""
from __future__ import annotations

import argparse
from bisect import bisect_left
import hashlib
import json
import os
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
    parser.add_argument('--lean-root', type=Path, help='Byte-identical compiled standalone checkout')
    parser.add_argument('--lake-bin', default='lake', help='Authorized lake lean wrapper')
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
    lean_root = (args.lean_root or repo / 'ReasBook').resolve()
    all_sources = {path.relative_to(paper).with_suffix('').as_posix().replace('/', '.'): path
                   for directory in ('ReasLib', 'DFPWolfe')
                   for path in (paper / directory).rglob('*.lean')}
    for name in ('DFPWolfe', 'ReasLib'):
        all_sources[name] = paper / (name + '.lean')
    owned = set()
    def visit(module):
        if module in owned or module not in all_sources:
            return
        owned.add(module)
        for dep in re.findall(r'^(?:(?:public|private)\s+)?import\s+(?:all\s+)?([\w.]+)',
                              mask_comments(all_sources[module].read_text()), re.MULTILINE):
            visit(dep)
    visit('DFPWolfe.V21.Paper')
    files = sorted(all_sources[module] for module in owned)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    for path in files:
        relative = path.relative_to(repo).as_posix()
        committed = subprocess.check_output(['git', 'show', f'{commit}:{relative}'], cwd=repo)
        if committed != path.read_bytes():
            raise RuntimeError('Commit the Lean source before extraction: ' + relative)
        compiled_source = lean_root / path.relative_to(paper) if args.lean_root else path
        if compiled_source.read_bytes() != committed:
            raise RuntimeError('Compiled workspace source differs: ' + relative)
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
        'moduleName.toString.startsWith "ReasLib." ||\n'
        '  moduleName.toString.startsWith "DFPWolfe."')
    # Retain compiler declaration ranges for exact source excerpts below each statement.
    text = text.replace('  line : Nat\n', '  line : Nat\n  endLine : Nat\n  endColumn : Nat\n', 1)
    text = text.replace('    line\n    kind :=',
        '    line\n    endLine := ranges?.map (·.range.endPos.line) |>.getD line\n'
        '    endColumn := ranges?.map (·.range.endPos.column) |>.getD 0\n    kind :=', 1)
    # Import private proof bodies as well as public interfaces. Missing theorem or
    # opaque bodies must fail extraction rather than silently erase graph edges.
    text = text.replace('roots.map fun root => { module := root.toName }',
                        'roots.map fun root => { module := root.toName, importAll := true }')
    guard = '  let docString := (← findDocString? env name (includeBuiltin := false)).getD ""'
    text = text.replace(guard, '  if (match info with | .thmInfo _ => true | .opaqueInfo _ => true | _ => false) && (info.value? (allowOpaque := true)).isNone then\n    throwError "Missing project proof body for {name}"\n' + guard)
    evidence.mkdir(parents=True)
    # Keep the SDK's temporary protocol files on the same persistent volume.
    tempfile.tempdir = str(evidence)

    def bounded_runner(command, **kwargs):
        command = list(command)
        config_path = Path(command[-2])
        config = json.loads(config_path.read_text())
        for spec in config['projects']:
            spec.setdefault('rootModules', [])
        config_path.write_text(json.dumps(config))
        config['projects'][0]['rootModules'] = ['DFPWolfe.Paper', 'DFPWolfe.V21.Paper']
        config_path.write_text(json.dumps(config))
        # The proof workspace authorizes `lake lean <file>`, rather than
        # `lake env lean --run`. Execute the SDK's IO exporter via a temporary
        # top-level #eval, retaining exactly the same config and output protocol.
        exporter = Path(command[command.index('--run') + 1])
        evaluation = evidence / 'ExtractEnvironment.lean'
        evaluation.write_text(exporter.read_text() + '\n#eval main ' +
            json.dumps([str(config_path), str(command[-1])]) + '\n')
        environment = dict(os.environ, LEAN_NUM_THREADS='1')
        command = [args.lake_bin, 'lean', str(evaluation)]
        kwargs['cwd'] = lean_root
        kwargs['env'] = environment
        result = subprocess.run(command, **kwargs)
        (evidence / 'extraction.log').write_text(result.stdout + result.stderr)
        return result

    project = Project('papers', 'Papers', 'Paper', 'DFP_wolfe_local', paper, 'DFPWolfe.V21.Paper')
    if args.reuse_evidence:
        saved_root = args.reuse_evidence.resolve()
        saved = json.loads((saved_root / 'provenance.json').read_text())
        source_identity = [dict(file=path.relative_to(paper).as_posix(), sha256=digest(path))
                           for path in files]
        if (saved['sourceCommit'] != commit or saved['sources'] != source_identity or
                saved['extractorSha256'] != digest(original) or
                saved.get('adaptedExtractorSha256') != hashlib.sha256(text.encode()).hexdigest() or
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
    source_identity = [dict(file=path.relative_to(paper).as_posix(), sha256=digest(path)) for path in files]
    (evidence / 'provenance.json').write_text(json.dumps(dict(sourceCommit=commit, sources=source_identity, extractorSha256=digest(original), adaptedExtractorSha256=hashlib.sha256(text.encode()).hexdigest(), rawSha256=digest(evidence / 'raw.json')), indent=2) + '\n')
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
                column=m.start('kind') - source.rfind('\n', 0, m.start('kind')) - 1,
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
        start_column = next(r['column'] for r in heads[item['file']] if r['line'] == begin and not r['private'])
        code = (''.join(lines[begin - 1:end - 1]) + lines[end - 1][:column])[start_column:]
        if not re.match(r'\s*(?:theorem|lemma)\s+', code):
            raise RuntimeError('Source excerpt does not begin at a declaration')
        items.append(dict(id=item['name'], label=label, title=label, type='Theorem',
            section=section_ids[group], file=item['file'], line=item['line'],
            declaration=item['name'], statement=item['docString'],
            dependencyEvidence='compiled', leanCode=code, endLine=end,
            sourceSha256=digest(paper / item['file']), **dependencies))
    source_hash = hashlib.sha256(json.dumps(sources, sort_keys=True).encode()).hexdigest()
    data = dict(schemaVersion=2, project=dict(id=project.project_id,
        title='DFP v21: complete polar proof and source refinements', kind='papers', branch='v4.32.0',
        commit=commit, repository='https://github.com/optpku/ReasBook',
        sourceRoot=project.source_root), sections=sections, items=items,
        generation=dict(mode='lean-environment', rootModule=project.root_module,
            compiledItemCount=len(items), sourceInventoryItemCount=expected,
            sourceOnlyItemCount=0, mergedItemCount=len(items), dependencyCoverage='complete',
            dependencyModel='statement-and-proof-v1', sourceSha256=source_hash,
            extractorSha256=digest(original), scope='Complete v21 numbered results 1–8 and source refinements; Section 6 interpolation retains its explicit disjoint-ball premise. Includes reused infrastructure in the v21 import closure.',
            sourceSnapshot='28f062c4d545c579a794a50593cf144b31c51cd5', rawDeclarationCount=len(raw),
            sourceModuleCount=len(files)))
    copy_generic_map(sdk / 'src/theorem_graph_sdk/resources/assets', output, data)
    mapping = json.loads(Path(__file__).with_name('v21_results.json').read_text())
    bundles = mapping['items']
    overview = project_graph(data, mapping)
    verify(data, overview)
    from generate_paper_graph import attach_statements
    excerpts = json.loads((paper / 'theorem-map/v21/paper-statements.json').read_text())
    attach_statements(overview, excerpts)
    by_name = {item['declaration']: item for item in items}
    for item, bundle in zip(overview['items'], bundles):
        names = bundle['declarations']
        primary = by_name[names[0]]
        item.update({key: primary[key] for key in ('declaration', 'file', 'line', 'endLine')})
        item['leanCode'] = primary['leanCode']
        item['leanExcerpts'] = [{key: by_name[name][key] for key in
            ('declaration', 'file', 'line', 'leanCode')} for name in names]
        item['statementHtml'] = next(row['statementHtml'] for row in excerpts['items']
                                     if row['id'] == item['id'])
    (output / 'overview-data.json').write_text(json.dumps(overview, indent=2, ensure_ascii=False) + '\n')
    (output / 'paper-statements.json').write_text(json.dumps(excerpts, ensure_ascii=False, indent=2) + '\n')
    # Only the v21 viewer gains a source panel; the original map is preserved.
    app = output / 'app.js'
    javascript = app.read_text()
    marker = '    var relationSection = document.createElement("section");'
    panel = '''    if (item.leanCode) {
      var codeSection = document.createElement("section");
      codeSection.className = "detail-section lean-code-section";
      var codeHeading = document.createElement("h3");
      codeHeading.textContent = "Corresponding Lean code";
      codeSection.appendChild(codeHeading);
      (item.leanExcerpts || [item]).forEach(function (excerpt) {
        var sourceLink = document.createElement("a");
        sourceLink.className = "detail-source-link";
        sourceLink.textContent = excerpt.declaration;
        sourceLink.href = sourceUrl(excerpt);
        sourceLink.target = "_blank";
        sourceLink.rel = "noreferrer";
        var pre = document.createElement("pre");
        pre.className = "lean-code-block";
        pre.tabIndex = 0;
        pre.setAttribute("aria-label", "Original Lean declaration and proof");
        var code = document.createElement("code");
        code.innerHTML = window.DFPLeanCode.highlight(excerpt.leanCode);
        pre.appendChild(code);
        codeSection.appendChild(sourceLink);
        codeSection.appendChild(pre);
      });
    }

'''
    if javascript.count(marker) != 1:
        raise RuntimeError('Review changed SDK detail renderer before regenerating')
    javascript = javascript.replace(marker, panel + marker)
    javascript = javascript.replace(
        '    refs.detailContent.replaceChildren(header, statementSection, relationSection, leanSection);',
        '    refs.detailContent.replaceChildren(header, statementSection);\n'
        '    if (item.leanCode) refs.detailContent.appendChild(codeSection);\n'
        '    refs.detailContent.append(relationSection, leanSection);')
    javascript = javascript.replace('fetch("./data.json",',
        'fetch(new URLSearchParams(window.location.search).get("view") === "lean" ? "./data.json" : "./overview-data.json",')
    javascript = javascript.replace('statementHeading.textContent = "Natural-language statement";',
        'statementHeading.textContent = item.paperMapping ? "Original paper statement" : "Declaration description";')
    app.write_text(javascript)
    css = output / 'styles.css'
    css.write_text(css.read_text() + '\n.detail-scroll { grid-column: 2; }\n'
        '.version-links { padding: .5rem 1rem; background: #f6f8fa; }\n'
        '.statement .katex { font-size: 1em; }\n'
        '.statement .katex-display { max-width: 100%; overflow-x: auto; overflow-y: hidden; padding: 8px 0; }\n'
        '.statement .katex-display > .katex { width: max-content; min-width: 100%; }\n'
        '.statement .katex-display .katex-html { display: inline-flex; align-items: baseline; justify-content: center; min-width: max-content; width: 100%; }\n'
        '.statement .katex-display .katex-html > .tag { position: static; margin-left: 1em; }\n')
    index = output / 'index.html'
    index.write_text(index.read_text().replace('</head>', '<link rel="stylesheet" href="../vendor/katex/katex.min.css">\n<link rel="stylesheet" href="../lean-code.css"></head>').replace('<script src="./app.js">', '<script src="../lean-code.js"></script>\n<script src="./app.js">').replace('<body>', '<body class="v21-view">\n<nav class="version-links">'
        '<a href="../index.html?view=paper">Original center-manifold proof</a> · '
        '<strong>v21 complete polar proof</strong> · '
        '<a href="?view=paper">Paper theorem numbers</a> · <a href="?view=lean">Lean declarations</a></nav>', 1))
    (evidence / 'provenance.json').write_text(json.dumps(dict(sourceCommit=commit,
        sources=sources, sourceSha256=source_hash, extractorSha256=digest(original),
        adaptedExtractorSha256=hashlib.sha256(text.encode()).hexdigest(), rawSha256=digest(evidence / 'raw.json')), indent=2) + '\n')
    print(json.dumps(dict(output=str(output), nodes=len(items),
        edges=sum(len(item['dependencies']) for item in items), sourceCommit=commit), indent=2))


if __name__ == '__main__':
    main()
