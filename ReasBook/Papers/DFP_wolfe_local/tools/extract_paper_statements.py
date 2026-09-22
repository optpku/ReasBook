#!/usr/bin/env python3
"""Extract exact numbered statements and typeset them without rewriting prose.

Requires pandoc and a JSON-in/JSON-out KaTeX renderer supplied with --renderer.
Only theorem-environment contents are exported, not the complete manuscript.
"""
import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import subprocess


BLOCK = re.compile(r'\\begin\{(theorem|lemma|corollary|proposition)\}(?:\[[^\n]*\])?'
                   r'(?P<body>[\s\S]*?)\\end\{\1\}')
LABEL = re.compile(r'\\label\{([^}]+)\}')
REF = re.compile(r'\\(eqref|ref)\{([^}]+)\}')
ENV = re.compile(r'\\begin\{(align\*?|equation\*?)\}([\s\S]*?)\\end\{\1\}')
MATH = re.compile(r'<span class="math (inline|display)">([\s\S]*?)</span>')


def digest(value):
    return hashlib.sha256(value).hexdigest()


def extract(manuscript, aux, mapping):
    references = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^{}]*)\}', aux))
    blocks = list(BLOCK.finditer(manuscript))
    if len(blocks) != len(mapping['items']):
        raise ValueError('Manuscript theorem inventory differs from reviewed mapping')
    statements = []
    for block, item in zip(blocks, mapping['items']):
        latex = block['body'].strip()
        labels = LABEL.findall(latex)
        if item['texLabel'] not in labels:
            raise ValueError(f'Missing label {item["texLabel"]}')
        number = references[item['texLabel']]
        if item['label'] != f'{block[1].title()} {number}':
            raise ValueError(f'Number mismatch for {item["texLabel"]}')
        refs = {label: references[label] for _, label in REF.findall(latex)}
        equation_labels = {label: references[label] for label in labels if label != item['texLabel']}
        statements.append(dict(id=item['id'], label=item['label'], texLabel=item['texLabel'],
            statementLatex=latex, statementSha256=digest(latex.encode()),
            sourceStartLine=manuscript.count('\n', 0, block.start()) + 1,
            sourceEndLine=manuscript.count('\n', 0, block.end()) + 1,
            references=refs, equationNumbers=equation_labels))
    return statements


def display_latex(statement):
    """Resolve cross-references and preserve equation numbers for static math."""
    refs = statement['references']
    numbers = statement['equationNumbers']
    text = statement['statementLatex']
    text = REF.sub(lambda m: '(' + refs[m[2]] + ')' if m[1] == 'eqref' else refs[m[2]], text)

    def equation(match):
        rows = re.split(r'\\\\(?:\[[^\]]*\])?', match[2]) if match[1].startswith('align') else [match[2]]
        displays = []
        for row in rows:
            labels = LABEL.findall(row)
            clean = LABEL.sub('', row).strip()
            if not clean:
                continue
            if match[1].startswith('align'):
                clean = r'\begin{aligned}' + clean + r'\end{aligned}'
            if len(labels) > 1:
                raise ValueError('More than one equation label on a display row')
            if labels:
                clean += r'\tag{' + numbers[labels[0]] + '}'
            displays.append(r'\[' + clean + r'\]')
        return '\n\n' + '\n\n'.join(displays) + '\n\n'

    text = ENV.sub(equation, text)
    return LABEL.sub('', text)


def render(statements, renderer):
    fragments, formulas = [], []
    for statement in statements:
        result = subprocess.run(['pandoc', '-f', 'latex', '-t', 'html5', '--mathjax', '--wrap=none'],
                                input=display_latex(statement), text=True, capture_output=True, check=True)
        if result.stderr.strip():
            raise ValueError('Pandoc diagnostic: ' + result.stderr)
        fragment = result.stdout.strip()
        if re.search(r'<(?:script|iframe|object)\b', fragment, re.I):
            raise ValueError('Unexpected active content')
        matches = list(MATH.finditer(fragment))
        spans = []
        for match in matches:
            tex = html.unescape(match[2])[2:-2]
            spans.append((match.start(), match.end(), len(formulas)))
            formulas.append(dict(tex=tex, display=match[1] == 'display'))
        fragments.append((fragment, spans))
    result = subprocess.run(renderer, input=json.dumps(formulas), text=True,
                            capture_output=True, check=True)
    rendered = json.loads(result.stdout)
    if len(rendered) != len(formulas):
        raise ValueError('Math renderer returned the wrong formula count')
    for statement, (fragment, spans) in zip(statements, fragments):
        for start, end, index in reversed(spans):
            fragment = fragment[:start] + rendered[index] + fragment[end:]
        statement['statementHtml'] = fragment
        statement['formulaCount'] = len(spans)
    return len(formulas)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manuscript', type=Path, required=True)
    parser.add_argument('--aux', type=Path, required=True)
    parser.add_argument('--renderer', nargs='+', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manuscript, aux = args.manuscript.read_text(), args.aux.read_text()
    mapping = json.loads((root / 'tools/paper_results.json').read_text())
    statements = extract(manuscript, aux, mapping)
    count = render(statements, args.renderer)
    output = dict(schemaVersion=1, manuscriptName=args.manuscript.name,
                  manuscriptSha256=digest(args.manuscript.read_bytes()),
                  auxSha256=digest(args.aux.read_bytes()),
                  rendering='Pandoc LaTeX to HTML; KaTeX 0.16.22 HTML+MathML, strict mode; no prose rewriting',
                  formulaCount=count, items=statements)
    (root / 'theorem-map/paper-statements.json').write_text(json.dumps(output, ensure_ascii=False, indent=2) + '\n')
    print(f'Extracted {len(statements)} exact theorem statements; rendered {count} formulas.')


if __name__ == '__main__':
    main()
