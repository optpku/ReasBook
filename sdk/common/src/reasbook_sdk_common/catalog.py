"""One self-contained static catalog renderer for assembly and Pages projection."""

from __future__ import annotations

from collections.abc import Iterable
import html


_STYLE = """
:root { color-scheme: light dark; font-family: system-ui, sans-serif; line-height: 1.6; }
body { margin: 0; background: #f7f8fa; color: #172b3a; }
main { max-width: 64rem; margin: auto; padding: 2.5rem 1.25rem; }
h1 { line-height: 1.2; font-size: clamp(1.6rem, 4vw, 2.5rem); }
a { color: #205d89; text-underline-offset: .2em; overflow-wrap: anywhere; }
.catalog-list { list-style: none; padding: 0; display: grid; gap: .75rem;
  grid-template-columns: repeat(auto-fit, minmax(min(100%, 24rem), 1fr)); }
.catalog-list a { display: block; padding: 1rem; border: 1px solid #bac9d5;
  border-radius: .4rem; background: white; text-decoration: none; }
a:hover { text-decoration: underline; }
a:focus-visible { outline: 3px solid #ba6400; outline-offset: 3px; }
footer { margin-top: 2rem; font-size: .9rem; }
@media (prefers-color-scheme: dark) {
  body { background: #14212b; color: #e5edf4; }
  a { color: #a9d5f3; }
  .catalog-list a { background: #1c303f; border-color: #4a6578; }
}
"""


def catalog_page(title: str, entries: Iterable[tuple[str, str]]) -> str:
    """Render ordered (label, URL) pairs; callers select existing local targets.

    Inline CSS keeps catalogs usable at any projection depth, with no asset
    dependency or JavaScript. Escape both titles and links as untrusted text.
    """
    links = ''.join(f'<li><a href="{html.escape(url, quote=True)}">'
                    f'{html.escape(label)}</a></li>' for label, url in entries)
    title = html.escape(title)
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{title}</title><style>{_STYLE}</style></head><body>'
            f'<main id="main-content"><h1>{title}</h1>'
            '<p>Read mathematical statements and Lean documentation.</p>'
            + (f'<ul class="catalog-list">{links}</ul>' if links else
               '<p>No project artifacts are published here yet.</p>')
            + '<footer><a href="https://github.com/optpku/ReasBook#readme">'
            'Project information on GitHub</a></footer></main></body></html>\n')
