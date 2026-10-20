#!/usr/bin/env python3
"""Quote the eight v21 statements verbatim and render their mathematical notation.

The supported source has global equation numbering, one ordinary align, no
explicit tags, no counter resets, and a shared theorem counter. Fail closed if
those conventions change. The full manuscript is never copied to the repo.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from extract_paper_statements import extract, render


def reference_numbers(source):
    if re.search(r'\\(?:tag|setcounter|numberwithin|counterwithin|notag|nonumber)\b', source):
        raise ValueError('Review changed source numbering conventions')
    result = {}
    number = 0
    pattern = re.compile(r'\\begin\{(equation|align)\}([\s\S]*?)\\end\{\1\}')
    for block in pattern.finditer(source):
        rows = re.split(r'\\\\(?:\[[^\]]*\])?', block[2]) if block[1] == 'align' else [block[2]]
        for row in rows:
            if not row.strip():
                continue
            number += 1
            for label in re.findall(r'\\label\{([^}]+)\}', row):
                if label in result:
                    raise ValueError('Duplicate equation label: ' + label)
                result[label] = str(number)
    theorem = re.compile(r'\\begin\{(theorem|lemma|corollary|proposition)\}([\s\S]*?)\\end\{\1\}')
    for index, block in enumerate(theorem.finditer(source), 1):
        label = re.findall(r'\\label\{([^}]+)\}', block[2])[0]
        result[label] = str(index)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manuscript', required=True, type=Path)
    p.add_argument('--renderer', required=True, nargs='+')
    a = p.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = a.manuscript.read_text()
    mapping = json.loads((root / 'tools/v21_results.json').read_text())
    refs = reference_numbers(source)
    aux = '\n'.join('\\newlabel{' + key + '}{{' + value + '}{}}' for key, value in refs.items())
    statements = extract(source, aux, mapping)
    count = render(statements, a.renderer)
    data = dict(schemaVersion=1, manuscriptName='October 9, 2026 v21 submission',
                manuscriptSha256=hashlib.sha256(a.manuscript.read_bytes()).hexdigest(),
                referenceNumbering='Global equation/align counters and shared theorem counter; explicit tags and counter changes rejected',
                references=refs, formulaCount=count,
                rendering='Verbatim statement excerpts; Pandoc and KaTeX 0.16.22 HTML+MathML; no prose rewriting',
                items=statements)
    (root / 'theorem-map/v21/paper-statements.json').write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(dict(statements=len(statements), formulas=count)))


if __name__ == '__main__':
    main()
