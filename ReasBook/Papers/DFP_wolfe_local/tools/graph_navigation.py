"""Install the same proof-route navigation in all three DFP viewers."""
from pathlib import Path
import re


def install_navigation(graph_root: Path, route: str) -> None:
    prefix = "./" if route == "original" else "../"
    destinations = [("original", "index.html?view=paper", "Center-manifold proof"),
                    ("latest", "latest/index.html", "Polar proof"),
                    ("v21", "v21/index.html?view=paper", "v21 archive")]
    links = []
    for key, path, label in destinations:
        attributes = ' aria-current="page"' if key == route else ""
        if key == "v21":
            attributes += ' class="archive-link"'
        links.append(f'<a href="{prefix}{path}"{attributes}>{label}</a>')
    nav = ('<nav class="proof-navigation" aria-label="Proof route">'
           '<span class="navigation-label">DFP proofs</span>' + "".join(links) + '</nav>')
    page = graph_root / 'index.html'
    if not page.is_file():
        return  # The data generator also supports a fresh JSON-only output.
    text = page.read_text()
    text = re.sub(r'<nav class="(?:version-links|proof-navigation)"[\s\S]*?</nav>\s*', '', text)
    text = re.sub(r'(<body[^>]*>)', lambda m: m.group(1) + '\n' + nav, text, count=1)
    stylesheet = f'<link rel="stylesheet" href="{prefix}proof-navigation.css">'
    if stylesheet not in text:
        text = text.replace('</head>', stylesheet + '\n</head>')
    if route == 'v21' and 'id="paperViewLink"' not in text:
        text = text.replace('<div class="index-controls">', '<div class="index-controls">'
            '<nav class="view-switch" aria-label="Node labels">'
            '<a id="paperViewLink" href="?view=paper">Paper numbers</a> '
            '<a id="leanViewLink" href="?view=lean">Lean declarations</a></nav>')
    page.write_text(text)
    # Keep arrowhead styling separate from fallback path styling on regeneration.
    css = graph_root / 'styles.css'
    if css.exists():
        styles = css.read_text()
        styles = re.sub(r'(?m)^\.graph-edge(?=[ {.])', 'path.graph-edge', styles)
        styles = styles.replace('path.graph-edge.dim', '.graph-edge.dim')
        css.write_text(styles)
    app = graph_root / 'app.js'
    if route == 'v21' and app.exists():
        script = app.read_text()
        marker = '    data = payload;'
        selection = """    ['paper', 'lean'].forEach(function (view) {
      var link = document.getElementById(view + 'ViewLink');
      var selected = new URLSearchParams(window.location.search).get('view') === 'lean' ? 'lean' : 'paper';
      if (link && view === selected) link.setAttribute('aria-current', 'page');
    });
"""
        if "getElementById(view +" not in script and "paperViewLink" not in script:
            script = script.replace(marker, selection + marker)
        app.write_text(script)
