// Static KaTeX rendering: no executable math content or browser CDN dependency.
// Usage: node render_paper_math.cjs /path/to/katex/dist/katex.js
const fs = require('node:fs');
const katex = require(process.argv[2] || 'katex');
if (katex.version !== '0.16.22') throw new Error('Use KaTeX 0.16.22 for reproducible output');
const formulas = JSON.parse(fs.readFileSync(0, 'utf8'));
const rendered = formulas.map(({tex, display}) => katex.renderToString(tex, {
  displayMode: display,
  throwOnError: true,
  strict: 'error',
  trust: false,
  output: 'htmlAndMathml',
  macros: {
    '\\R': '\\mathbb{R}',
    '\\norm': '\\lVert #1\\rVert',
    '\\ip': '\\langle #1,#2\\rangle'
  }
}));
process.stdout.write(JSON.stringify(rendered));
