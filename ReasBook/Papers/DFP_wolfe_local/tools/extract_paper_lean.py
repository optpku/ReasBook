#!/usr/bin/env python3
"""Export exact Lean code below the paper statements using doc-gen ranges."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sqlite3


def excerpt(source, start_line, end_line, end_column):
    """Slice a compiler-provided source range (one-based lines, zero-based columns)."""
    lines = source.splitlines(keepends=True)
    if not 1 <= start_line <= end_line <= len(lines):
        raise ValueError('Invalid declaration line range')
    if not 0 <= end_column <= len(lines[end_line - 1].rstrip('\r\n')):
        raise ValueError('Invalid declaration end column')
    return ''.join(lines[start_line - 1:end_line - 1]) + lines[end_line - 1][:end_column]


def extract(root, docs_root, graph):
    manifest = json.loads((docs_root / 'project-docs.json').read_text())
    hashes = {item['module']: item['sha256'] for item in manifest['sources']}
    database = docs_root / 'api-docs.db'
    declarations = {}
    with sqlite3.connect(database.as_uri() + '?mode=ro', uri=True) as connection:
        for item in graph['items']:
            for declaration in item['relatedDeclarations']:
                name = declaration['declaration']
                if name in declarations:
                    continue
                rows = connection.execute('''
                    SELECT n.module_name, r.start_line, r.end_line, r.end_column
                    FROM name_info n JOIN declaration_ranges r USING (module_name, position)
                    WHERE n.name = ?
                ''', (name,)).fetchall()
                if len(rows) != 1:
                    raise ValueError(f'Expected one compiled range for {name}')
                module, begin, end, column = rows[0]
                relative = Path(*module.split('.')).with_suffix('.lean')
                if relative.as_posix() != declaration['file']:
                    raise ValueError(f'Module mapping changed for {name}')
                path = root / relative
                file_bytes = path.read_bytes()
                file_hash = hashlib.sha256(file_bytes).hexdigest()
                if hashes.get(module) != file_hash:
                    raise ValueError(f'Source differs from the documented snapshot: {path}')
                start = declaration['line']
                if not begin <= start <= end:
                    raise ValueError(f'Graph anchor outside compiled declaration range: {name}')
                source = file_bytes.decode()
                code = excerpt(source, start, end, column)
                head = re.match(r'\s*(?:theorem|lemma)\s+([^\s({:\[=]+)', code)
                if not head or not (name == head[1] or name.endswith('.' + head[1])):
                    raise ValueError(f'Extracted code does not start with {name}')
                declarations[name] = dict(declaration=name, file=relative.as_posix(),
                    startLine=start, endLine=end, endColumn=column, code=code,
                    codeSha256=hashlib.sha256(code.encode()).hexdigest(), sourceSha256=file_hash)
    return dict(schemaVersion=1, sourceCommit=manifest['revision'],
                toolchain=manifest['toolchain'], extraction='Verified doc-gen4 declaration ranges; original source text',
                declarations=declarations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--docs-root', type=Path, required=True,
                        help='Verified project-docs directory with api-docs.db and project-docs.json')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    graph = json.loads((root / 'theorem-map/paper-data.json').read_text())
    data = extract(root, args.docs_root.resolve(), graph)
    (root / 'theorem-map/paper-lean.json').write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    print(f'Exported {len(data["declarations"])} exact Lean declarations with proofs.')


if __name__ == '__main__':
    main()
