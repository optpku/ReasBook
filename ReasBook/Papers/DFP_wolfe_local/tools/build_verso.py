#!/usr/bin/env python3
"""Render the eight DFP Verso routes from freshly extracted Lean source.

The source project must have been checked and committed. A disposable web
workspace uses version-matched, prebuilt package caches copied from --web-cache.
No lake build, dependency update, live deployment, or source-tree edit occurs.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def prepare_presentation(web):
    """Keep the paper landing route and long source blocks usable on phones."""
    routes = web / 'ReasBookSite/RouteTable.lean'
    text = routes.read_text()
    module = 'ReasBookSite.WorkPages.Papers.DFP_wolfe_local'
    if 'import ' + module not in text:
        text = text.replace('import Book\n', 'import Book\nimport ' + module + '\n')
        for indentation in ('      ', '  '):
            line = indentation + 'static "static" ← "./static_files"\n'
            # Anchored replacement avoids matching the shorter indentation inside a longer line.
            text = text.replace('\n' + line, '\n' + line + indentation +
                                '"papers/dfp_wolfe_local/" ' + module + '\n')
        routes.write_text(text)
    fragment = web / '.project-fragment.json'
    data = json.loads(fragment.read_text())
    data['routes'] = sorted(set(data['routes']) | {'papers/dfp_wolfe_local/'})
    fragment.write_text(json.dumps(data, indent=2) + '\n')
    site = web / 'ReasBookSite.lean'
    text = site.read_text()
    if '<meta name="viewport"' not in text:
        text = text.replace('<meta charset="UTF-8"/>',
            '<meta charset="UTF-8"/>\n          <meta name="viewport" content="width=device-width, initial-scale=1"/>')
    marker = '    if (u.origin !== window.location.origin) return href;'
    replacement = marker + '''
    // Preserve cross-project catalog and resource aliases.
    if (u.pathname.startsWith("/ReasBook/sites/") ||
        u.pathname.startsWith("/ReasBook/theorem-maps/")) return href;'''
    if 'Preserve cross-project catalog and resource aliases.' not in text:
        text = text.replace(marker, replacement)
    site.write_text(text)
    css = web / 'static_files/style.css'
    text = css.read_text()
    if 'DFP reading-page source blocks' not in text:
        css.write_text(text + '''
/* DFP reading-page source blocks scroll without widening the page. */
div.main, div.wrap, article { min-width: 0; }
code.hl.lean.block, pre { display: block; max-width: 100%; overflow-x: auto; }
p code, li code { overflow-wrap: anywhere; }
''')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tooling-root', type=Path, required=True,
                        help='Clean ReasBook checkout containing ReasBookWeb/scripts')
    parser.add_argument('--web-cache', type=Path, required=True,
                        help='Existing ReasBookWeb directory with matching prebuilt dependencies')
    parser.add_argument('--workspace', type=Path, required=True,
                        help='New disposable directory outside the source repository')
    args = parser.parse_args()
    paper = Path(__file__).resolve().parents[1]
    lean_root = paper.parents[1]
    repo = lean_root.parent
    workspace = args.workspace.resolve()
    if workspace.exists() or workspace == repo or repo in workspace.parents:
        parser.error('workspace must be a new directory outside the source repository')
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    if subprocess.check_output(['git', 'diff', 'HEAD', '--',
            'ReasBook/Papers/DFP_wolfe_local/**/*.lean',
            'ReasBook/Papers/DFP_wolfe_local/*.lean'], cwd=repo):
        raise RuntimeError('Commit the Lean source before extracting the reading pages')
    web_source = repo / 'ReasBookWeb'
    cache_source = args.web_cache.resolve()
    for name in ('lean-toolchain', 'lake-manifest.json'):
        if (web_source / name).read_bytes() != (cache_source / name).read_bytes():
            raise RuntimeError(f'Web cache has a different {name}')
    plan = json.loads((paper / 'tools/verso_modules.json').read_text())
    modules = plan['modules']
    workspace.mkdir(parents=True)
    (workspace / 'ReasBook').symlink_to(lean_root, target_is_directory=True)
    web = workspace / 'ReasBookWeb'
    shutil.copytree(web_source, web, ignore=shutil.ignore_patterns('.lake', '__pycache__'))
    packages = web / '.lake/packages'
    packages.parent.mkdir()
    # Copy-on-write where supported; never mutate the shared cache via hardlinks.
    subprocess.run(['cp', '-a', '--reflink=auto', str(cache_source / '.lake/packages'),
                    str(packages)], check=True)
    literate = workspace / 'literate'
    logs = workspace / 'logs'
    logs.mkdir()
    env = {**os.environ, 'LEAN_NUM_THREADS': '1', 'DFP_LITERATE_CACHE': str(literate)}

    def run(argv, cwd, log, timeout=7200):
        if argv[0] == 'lake' and 'build' in argv:
            raise RuntimeError('lake build is disabled in this adapter')
        with (logs / log).open('w') as stream:
            result = subprocess.run(['taskset', '-c', '0-1', *argv], cwd=cwd, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
        if result.returncode:
            raise RuntimeError(f'{log}: exit {result.returncode}; inspect {logs / log}')

    sources = []
    for row in modules:
        module = row['module']
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = paper / relative
        before = hashlib.sha256(source.read_bytes()).hexdigest()
        output = literate / relative.with_suffix('.json')
        output.parent.mkdir(parents=True, exist_ok=True)
        print('Extracting', module, flush=True)
        run(['lake', 'env', 'lean', '-j1', '-M8192', '--run',
             '.lake/packages/subverso/ExtractModule.lean', module, str(output)],
            lean_root, row['slug'] + '.log')
        if before != hashlib.sha256(source.read_bytes()).hexdigest():
            raise RuntimeError(f'Source changed during extraction: {module}')
        if not json.loads(output.read_text()).get('items'):
            raise RuntimeError(f'No source items extracted for {module}')
        sources.append({**row, 'file': relative.as_posix(), 'sourceSha256': before,
                        'literateSha256': hashlib.sha256(output.read_bytes()).hexdigest()})
        print('Extracted', module, output.stat().st_size, 'bytes', flush=True)

    os.environ.update(REASBOOK_INCLUDE_PROJECTS='papers/DFP_wolfe_local',
        REASBOOK_PROJECT_FRAGMENT='1', REASBOOK_GITHUB_REPO='optpku/ReasBook',
        REASBOOK_GITHUB_BRANCH=revision, REASBOOK_SITE_ROOT='/ReasBook/versions/v4.32.0/')
    scripts = args.tooling_root.resolve() / 'ReasBookWeb/scripts'
    sys.path.insert(0, str(scripts))
    spec = importlib.util.spec_from_file_location('gen_sections', scripts / 'gen_sections.py')
    gen = importlib.util.module_from_spec(spec)
    sys.modules['gen_sections'] = gen
    spec.loader.exec_module(gen)
    entries = [gen.Entry('papers', row['module'], row['title'],
        f"papers/dfp_wolfe_local/sections/{row['slug']}/", 'DFP_wolfe_local',
        0, index + 1, 0, row['slug']) for index, row in enumerate(modules)]
    gen.PAPER_TITLES['DFP_wolfe_local'] = 'DFP: nonconvergence and planar convergence'
    gen.collect_entries = lambda *args: entries
    gen.parse_args = lambda: argparse.Namespace(repo_root=str(workspace), repo_root_option=None)
    gen.main()

    sections = web / 'ReasBookSite/Sections.lean'
    contents = sections.read_text()
    contents = contents.replace('/ReasBook/versions/v4.32.0/docs/ReasBook/',
                                '/ReasBook/versions/v4.32.0/docs/DFP_wolfe_local/')
    sections.write_text(contents)
    landing = web / 'ReasBookSite/WorkPages/Papers/DFP_wolfe_local.lean'
    lines = ['import VersoBlog', 'open Verso Genre Blog', '',
        '#doc (Page) "Classical DFP under Wolfe conditions" =>', '',
        'The formalization covers a strong Wolfe nonconvergence counterexample, its sharp one-half Hölder Hessian regularity, and planar convergence under a locally Lipschitz Hessian.', '',
        '[API documentation](/ReasBook/sites/dfp_wolfe_local/docs/) · '
        '[Theorem dependency map](/ReasBook/theorem-maps/papers/dfp_wolfe_local/) · '
        f'[Lean source](https://github.com/optpku/ReasBook/tree/{revision}/ReasBook/Papers/DFP_wolfe_local/)', '',
        'The numbered theorem map quotes the original paper statements above their corresponding Lean proofs. These reading pages show the complete source of eight central modules.', '',
        '# Reading guide', '']
    for row in modules:
        lines.append(f"- [{row['title']}](/ReasBook/versions/v4.32.0/papers/dfp_wolfe_local/sections/{row['slug']}/)")
    lines += ['', '# Formalization', '', 'Zichen Wang. Lean 4.32.0. Apache License 2.0.', '']
    landing.write_text('\n'.join(lines))

    loader = web / 'ReasBookSite/LiterateModule.lean'
    contents = loader.read_text()
    begin = contents.index('  let f ← IO.FS.Handle.mk lakeConfig .read')
    end = contents.index('  let parsed ←', begin)
    contents = contents[:begin] + '''  let some cache ← IO.getEnv "DFP_LITERATE_CACHE"
    | throw <| IO.userError "DFP_LITERATE_CACHE must identify the verified JSON cache"
  let path := (cache : System.FilePath) / ((mod.replace "." "/") ++ ".json")
  let jsonFile ← IO.FS.readFile path

''' + contents[end:]
    loader.write_text(contents)
    lakefile = web / 'lakefile.lean'
    contents = lakefile.read_text().split('/-- Root of the main ReasBook project')[0]
    lakefile.write_text(contents + 'lean_lib Book where\n  srcDir := ".lake/build/src"\n')
    source_root = web / '.lake/build/src'
    imports = []
    for row in modules:
        module = row['module']
        wrapper = source_root / 'Book' / Path(*module.split('.')).with_suffix('.lean')
        wrapper.parent.mkdir(parents=True, exist_ok=True)
        wrapper.write_text('import ReasBookSite.LiterateModule\n\n'
            'set_option maxHeartbeats 100000000\nset_option maxRecDepth 20000\n\n'
            f'reasbook_page Book.{module} from {module} as {json.dumps(row["title"], ensure_ascii=False)}\n')
        imports.append('import Book.' + module)
    (source_root / 'Book.lean').write_text('\n'.join(imports) + '\n')
    prepare_presentation(web)
    print('Checking generated Verso entrypoint', flush=True)
    run(['lake', 'lean', 'ReasBookSite.lean', '--', '-j1', '-M8192'], web, 'verso-check.log')
    print('Rendering eight Verso routes', flush=True)
    run(['lake', 'env', 'lean', '-j1', '-M8192', '--run', 'ReasBookSite.lean',
         '--output', str(workspace / 'site')], web, 'verso-render.log')
    manifest = dict(schemaVersion=1, sourceCommit=revision, modules=sources,
                    toolchain=(lean_root / 'lean-toolchain').read_text().strip(),
                    siteRoot='/ReasBook/versions/v4.32.0/',
                    toolingCommit=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                        cwd=args.tooling_root, text=True).strip())
    (workspace / 'verso-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'output': str(workspace / 'site'), 'sourceCommit': revision,
                      'sections': len(modules)}), flush=True)


if __name__ == '__main__':
    main()
