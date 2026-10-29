"""One self-contained static catalog renderer for assembly and Pages projection."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
import html

from .attribution import project_credit, project_key_from_url


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
.catalog-list > li > a { display: block; padding: 1rem .5rem;
  font: 1.25rem/1.5 var(--reader-serif); text-decoration: none; }
.catalog-list > li > a:hover { background: var(--reader-navigation); text-decoration: underline; }
.catalog-credit { padding: 0 .5rem 1.25rem; color: var(--reader-muted);
  font-size: .9375rem; overflow-wrap: anywhere; }
.catalog-credit p { font: inherit; margin: .25rem 0; max-width: none; }
.catalog-credit .credit-source { font-size: .8125rem; }
.catalog-section { margin-top: 2.5rem; scroll-margin-top: 1rem; }
.catalog-section h2 { font: 400 1.75rem/1.3 var(--reader-serif); margin: 0; }
.catalog-section .catalog-list { margin-top: 1rem; }
.catalog-jump { display: flex; flex-wrap: wrap; gap: .5rem 1.5rem; margin-top: 1.5rem; }
.catalog-jump a { padding-block: .5rem; }
.catalog-note, .catalog-notice { color: var(--reader-muted); }
.catalog-note { margin: -.5rem .5rem .75rem; font: .875rem/1.5 system-ui, sans-serif; }
.catalog-notice { font: .9375rem/1.6 system-ui, sans-serif; border-left: 2px solid var(--reader-rule);
  padding-left: 1rem; }
a:focus-visible, main:focus-visible { outline: 2px solid var(--reader-link); outline-offset: 3px; }
::selection { background: var(--reader-navigation); color: var(--reader-ink); }
footer { margin-top: 2.5rem; color: var(--reader-muted); font-size: .875rem; }
@media (max-width: 640px) { main { padding-top: 2rem; } h1 { font-size: 2rem; } }
"""


@dataclass(frozen=True)
class CatalogEntry:
    label: str
    url: str
    project_key: str | None = None
    note: str = ""


def catalog_page(title: str, entries: Iterable[tuple[str, str] | CatalogEntry], *, notice: str = "") -> str:
    """Render ordered (label, URL) pairs; callers select existing local targets.

    Inline CSS keeps catalogs usable at any projection depth, with no asset
    dependency or JavaScript. Escape both titles and links as untrusted text.
    """
    groups: dict[str, list[str]] = {"books": [], "papers": [], "resources": []}
    for entry in entries:
        if not isinstance(entry, CatalogEntry):
            entry = CatalogEntry(*entry)
        label, url = entry.label, entry.url
        key = entry.project_key or project_key_from_url(url)
        credit = project_credit(key or "")
        byline = ''
        if credit:
            byline = ('<div class="catalog-credit"><p>Formalization contributors: '
                      + html.escape(', '.join(credit.names)) + '</p>')
            for role, names in credit.additional:
                byline += f'<p>{html.escape(role)}: {html.escape(", ".join(names))}</p>'
            byline += ('<p class="credit-source">Project-level credit · '
                       f'<a href="{html.escape(credit.source, quote=True)}">Source roster</a>'
                       '</p></div>')
        group = key.split('/')[0] if key else 'resources'
        if group not in groups:
            group = 'resources'
        note = f'<p class="catalog-note">{html.escape(entry.note)}</p>' if entry.note else ''
        groups[group].append(f'<li><a href="{html.escape(url, quote=True)}">'
                             f'{html.escape(label)}</a>{note}{byline}</li>')
    headings = {"books": "Books", "papers": "Papers", "resources": "Other resources"}
    populated = [key for key, links in groups.items() if links]
    jump = ('<nav class="catalog-jump" aria-label="Collection sections">'
            + ''.join(f'<a href="#{key}">{headings[key]}</a>' for key in populated) + '</nav>'
            if len(populated) > 1 else '')
    sections = ''
    for key in populated:
        items = '<ul class="catalog-list">' + ''.join(groups[key]) + '</ul>'
        sections += (items if populated == ['resources'] else
                     f'<section class="catalog-section" id="{key}" aria-labelledby="{key}-heading">'
                     f'<h2 id="{key}-heading">{headings[key]}</h2>{items}</section>')
    title = html.escape(title)
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<meta name="theme-color" content="#ffffff">'
            f'<title>{title}</title><style>{_STYLE}</style></head><body>'
            f'<main id="main-content"><h1>{title}</h1>'
            '<p>Mathematical textbooks and research papers formalized in Lean.</p>'
            + (f'<p class="catalog-notice">{html.escape(notice)}</p>' if notice else '')
            + jump
            + (sections if sections else
               '<p>No project artifacts are published here yet.</p>')
            + '<footer><a href="https://github.com/optpku/ReasBook#readme">'
            'Project information on GitHub</a></footer></main></body></html>\n')
