"""One self-contained static catalog renderer for assembly and Pages projection."""

from __future__ import annotations

from collections.abc import Iterable
import html


_STYLE = """
:root { color-scheme: light;
  --reader-surface: #ffffff; --reader-ink: #25232d; --reader-muted: #68636f;
  --reader-link: #514077; --reader-rule: #ddd9e3; --reader-navigation: #f5f5f8;
  --reader-serif: Georgia, "Times New Roman", "DejaVu Serif", serif;
  font-family: system-ui, sans-serif; line-height: 1.6; }
body { margin: 0; background: var(--reader-surface); color: var(--reader-ink); }
main { max-width: 54rem; margin: auto; padding: 3rem 1.25rem 4rem; }
h1 { font: 400 2.5rem/1.25 var(--reader-serif); max-width: 30ch;
  margin: 0 0 1rem; text-wrap: balance; overflow-wrap: anywhere; }
p { font: 1.125rem/1.75 var(--reader-serif); max-width: 72ch; }
a { color: var(--reader-link); text-underline-offset: .2em; overflow-wrap: anywhere; }
.catalog-list { list-style: none; padding: 0; margin-top: 2rem; }
.catalog-list li { border-top: 1px solid var(--reader-rule); }
.catalog-list a { display: block; padding: 1rem .5rem;
  font: 1.25rem/1.5 var(--reader-serif); text-decoration: none; }
.catalog-list a:hover { background: var(--reader-navigation); text-decoration: underline; }
a:focus-visible, main:focus-visible { outline: 2px solid var(--reader-link); outline-offset: 3px; }
::selection { background: var(--reader-navigation); color: var(--reader-ink); }
footer { margin-top: 2.5rem; color: var(--reader-muted); font-size: .875rem; }
@media (max-width: 640px) { main { padding-top: 2rem; } h1 { font-size: 2rem; } }
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
            '<meta name="theme-color" content="#ffffff">'
            f'<title>{title}</title><style>{_STYLE}</style></head><body>'
            f'<main id="main-content"><h1>{title}</h1>'
            '<p>Mathematical textbooks and research papers formalized in Lean.</p>'
            + (f'<ul class="catalog-list">{links}</ul>' if links else
               '<p>No project artifacts are published here yet.</p>')
            + '<footer><a href="https://github.com/optpku/ReasBook#readme">'
            'Project information on GitHub</a></footer></main></body></html>\n')
