#!/usr/bin/env python3
"""Build the final Pages tree from the merged version-branch site artifacts.

The branch artifacts use two historical layout conventions:

* v4.26 aggregate libraries publish Verso pages under ``books/<slug>/`` and
  ``papers/<slug>/``, and docs under ``docs/ReasBook/Books|Papers/<name>/``.
* v4.30+ per-project libraries publish Verso pages under ``<slug>/`` and docs
  under ``docs/ReasBook/<name>/``.  v4.32.2 historically published docs under
  ``docs/<name>/``.

This script normalizes all of those inputs into one canonical site:

* docs are always ``docs/ReasBook/Books|Papers/<name>/``
* each project gets a ``sites/<slug>/pages`` copy containing the richest
  available Verso tree, and ``sites/<slug>/docs`` containing its canonical docs
* other Verso assets/routes remain in place so absolute links inside copied
  pages continue to work
"""

from __future__ import annotations

import html
import json
import os
import re
import shutil
from collections import defaultdict
from pathlib import Path
from urllib.parse import unquote, urlsplit

from reader_entrypoints import write_reader_entrypoints


ASSETS_DIR = Path(__file__).resolve().parent / "assets"

_DOCUMENTATION_PAIR_RE = re.compile(
    r"\(\s*(?P<documentation><a\b[^>]*>\s*Documentation\s*</a>)\s*\)"
    r"(?P<separator>\s*)"
    r"\(\s*(?P<verso><a\b[^>]*>\s*Verso\s*</a>)\s*\)",
    flags=re.IGNORECASE,
)
_HREF_RE = re.compile(
    r"\bhref\s*=\s*(?P<quote>['\"])(?P<href>.*?)(?P=quote)",
    flags=re.IGNORECASE,
)
_SOURCE_DOCUMENTATION_PAIR_RE = re.compile(
    r"(?P<documentation><a\b[^>]*>\s*API documentation\s*</a>)"
    r"(?P<separator>\s*\)\s*\(\s*)"
    r"(?P<source><a\b[^>]*>\s*Lean source\s*</a>)",
    flags=re.IGNORECASE,
)
_UNAVAILABLE_DOCUMENTATION_MANIFEST = "unavailable-documentation.json"


def count_html(path: Path) -> int:
    if not path.is_dir():
        return 0
    return sum(1 for _ in path.rglob("*.html"))


def best_dir(candidates: list[Path]) -> Path | None:
    best: Path | None = None
    best_count = 0
    for candidate in candidates:
        count = count_html(candidate)
        if count > best_count:
            best = candidate
            best_count = count
    return best


def has_index(path: Path) -> bool:
    return (path / "index.html").is_file()


def display_name(identifier: str) -> str:
    """Turn a repository identifier into a readable, stable catalog label."""

    if identifier == "TR_LALM_theory":
        return "TR-LALM Theory"

    def humanize(value: str) -> str:
        words = value.replace("_", " ")
        words = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", words)
        words = re.sub(r"(?<=[A-Za-z])(?=[0-9])", " ", words)
        words = re.sub(r"\s+", " ", words).strip()
        return words.replace("Introductionto ", "Introduction to ")

    parts = identifier.rsplit("_", 2)
    if len(parts) == 3 and re.fullmatch(r"(?:19|20)\d{2}", parts[2]):
        title, author, year = humanize(parts[0]), humanize(parts[1]), parts[2]
        return f"{title} ({author}, {year})"
    return humanize(identifier) or identifier


def page_head(title: str, stylesheet: str) -> list[str]:
    escaped_title = html.escape(title)
    return [
        "<head>",
        '  <meta charset="utf-8" />',
        '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
        '  <meta name="theme-color" content="#17211c" />',
        f"  <title>{escaped_title}</title>",
        f'  <link rel="stylesheet" href="{html.escape(stylesheet, quote=True)}" />',
        "</head>",
    ]


def masthead(home_href: str, versions_href: str | None = None) -> list[str]:
    version_link = (
        f'<a class="masthead-link" href="{html.escape(versions_href, quote=True)}">'
        "Version Archive</a>"
        if versions_href
        else ""
    )
    return [
        '<a class="skip-link" href="#main-content">Skip to content</a>',
        '<header class="masthead">',
        '  <div class="masthead-inner">',
        f'    <a class="brand" href="{html.escape(home_href, quote=True)}">',
        '      <span class="proof-mark" aria-hidden="true">&#8866;</span>',
        "      <span><strong>ReasBook</strong><small>Formal Mathematics Library</small></span>",
        "    </a>",
        f"    {version_link}",
        "  </div>",
        "</header>",
    ]


def build_pages_tree(candidates: list[Path], dst: Path) -> None:
    """Copy the richest Verso tree, then guarantee ``dst/index.html``.

    The branch artifacts split a project's Verso landing page (often at
    ``<kind>/<slug>/index.html``) from its chapter/section routes (often at
    ``<slug>/...``).  ``best_dir`` alone can therefore produce a ``pages/``
    tree with content but no directory index, which GitHub Pages serves as a
    404.  Copy the richest tree first, overlay a landing index from any other
    candidate, and finally generate a minimal index for trees that never had
    one (for example the v4.26 aggregate library chapter trees).
    """
    present = [candidate for candidate in candidates if candidate.is_dir()]
    if not present:
        return

    content_src = best_dir(present)
    assert content_src is not None
    shutil.copytree(content_src, dst)

    if not has_index(dst):
        for candidate in present:
            if candidate != content_src and has_index(candidate):
                shutil.copy2(candidate / "index.html", dst / "index.html")
                break

    if not has_index(dst):
        write_pages_index(dst)


def write_pages_index(pages_dir: Path) -> None:
    """Generate a minimal landing page for a tree without a Verso index."""
    entries: list[tuple[str, str]] = []
    for child in sorted(pages_dir.iterdir()):
        if child.is_dir() and count_html(child) > 0:
            entries.append((f"./{child.name}/", child.name))

    (pages_dir / "index.html").write_text(
        html_page(
            "Pages",
            entries,
            "../",
            stylesheet="../../../static/catalog.css",
            home_href="../../../",
            eyebrow="Reading Index",
        ),
        encoding="utf-8",
    )


def write_docs_index(
    docs_dir: Path,
    leaf: str,
    *,
    stylesheet: str = "../../../static/catalog.css",
) -> None:
    """Add an index to a copied docs tree so ``./docs/`` is not a 404.

    The canonical docs tree contains ``Book.html``/``Paper.html`` plus module
    pages but has no directory index.  GitHub Pages does not render directory
    listings, so the site's ``Documentation`` nav link would otherwise 404 for
    every project.
    """
    (docs_dir / "index.html").write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                f'  <meta http-equiv="refresh" content="0; url=./{leaf}" />',
                "  <title>Documentation</title>",
                f'  <link rel="stylesheet" href="{html.escape(stylesheet, quote=True)}" />',
                "</head>",
                '<body class="redirect-page">',
                f'  <p><a href="./{leaf}">Open Documentation</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )


def write_redirect(path: Path, target: str, title: str) -> None:
    """Write a small, accessible redirect page to a preserved generated tree."""

    escaped_target = html.escape(target, quote=True)
    escaped_title = html.escape(title)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                f'  <meta http-equiv="refresh" content="0; url={escaped_target}" />',
                f"  <title>{escaped_title}</title>",
                "</head>",
                "<body>",
                f'  <p><a href="{escaped_target}">{escaped_title}</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )


def _site_base_path() -> str:
    value = os.environ.get("REASBOOK_SITE_ROOT", "/ReasBook/").strip()
    if not value.startswith("/"):
        value = "/" + value
    return value.rstrip("/") + "/"


def _anchor_href(anchor: str) -> str | None:
    match = _HREF_RE.search(anchor)
    return html.unescape(match.group("href")) if match else None


def _internal_link_target(
    site_root: Path,
    document: Path,
    href: str,
    *,
    base_path: str,
) -> Path | None:
    """Resolve one local static-site href without accepting path escapes."""

    parsed = urlsplit(href.strip())
    if parsed.scheme or parsed.netloc or not parsed.path:
        return None
    decoded_path = unquote(parsed.path)
    if decoded_path.startswith("/"):
        if not decoded_path.startswith(base_path):
            return None
        candidate = site_root / decoded_path[len(base_path) :].lstrip("/")
    else:
        candidate = document.parent / decoded_path

    resolved_root = site_root.resolve()
    candidate = candidate.resolve()
    if candidate != resolved_root and resolved_root not in candidate.parents:
        return None
    if decoded_path.endswith("/") or candidate.is_dir():
        candidate = candidate / "index.html"
    return candidate


def reconcile_documentation_links(
    site_root: Path, *, verified_source_links: dict[str, str] | None = None,
) -> dict[str, object]:
    """Make unavailable API links explicit while preserving strict closure.

    Verso intentionally renders source modules beyond a project's public
    ``Book``/``Paper`` import closure, while doc-gen publishes only that
    closure.  Historical artifacts therefore contain a small number of
    generated ``Documentation`` links for modules that have no API page.  A
    pair is downgraded only when its API target is absent *and* its adjacent
    Verso target exists.  Every other missing link remains untouched so the
    subsequent strict verifier still fails closed.

    An operator may additionally supply source URLs verified against pinned Git
    objects, mapped to their immutable commit URLs. Only adjacent generated
    API/Lean-source pairs with matching module names use that fallback. No API
    placeholder page is fabricated, and ordinary broken links are not waived.
    """

    base_path = _site_base_path()
    occurrences: dict[tuple[str, str], list[str]] = defaultdict(list)
    replacement_count = 0
    source_occurrences: dict[tuple[str, str], list[str]] = defaultdict(list)

    for document in sorted(site_root.rglob("*.html")):
        if document.is_symlink() or not document.is_file():
            continue
        source = document.read_text(encoding="utf-8", errors="replace")
        if not (("Documentation" in source and "Verso" in source) or
                (verified_source_links and "API documentation" in source)):
            continue

        relative_document = document.relative_to(site_root).as_posix()

        def replace(match: re.Match[str]) -> str:
            nonlocal replacement_count
            documentation = match.group("documentation")
            verso = match.group("verso")
            documentation_href = _anchor_href(documentation)
            verso_href = _anchor_href(verso)
            if documentation_href is None or verso_href is None:
                return match.group(0)

            documentation_target = _internal_link_target(
                site_root,
                document,
                documentation_href,
                base_path=base_path,
            )
            verso_target = _internal_link_target(
                site_root,
                document,
                verso_href,
                base_path=base_path,
            )
            if (
                documentation_target is None
                or documentation_target.is_file()
                or verso_target is None
                or not verso_target.is_file()
            ):
                return match.group(0)

            occurrences[(documentation_href, verso_href)].append(relative_document)
            replacement_count += 1
            return (
                '<span class="documentation-unavailable" '
                'title="This source module is not part of the published API '
                'documentation">Documentation unavailable</span>'
                + match.group("separator")
                + f"({verso})"
            )

        rendered = _DOCUMENTATION_PAIR_RE.sub(replace, source)
        def replace_source(match: re.Match[str]) -> str:
            nonlocal replacement_count
            if "docs" in document.relative_to(site_root).parts:
                return match.group(0)
            docs_href = _anchor_href(match.group("documentation"))
            source_href = _anchor_href(match.group("source"))
            pinned = (verified_source_links or {}).get(source_href or "")
            if not docs_href or not pinned or not re.fullmatch(
                r"https://github[.]com/[^/]+/[^/]+/blob/[0-9a-f]{40}/[^?#]+[.]lean", pinned
            ):
                return match.group(0)
            target = _internal_link_target(site_root, document, docs_href, base_path=base_path)
            if target is None or target.is_file() or target.stem != Path(urlsplit(pinned).path).stem:
                return match.group(0)
            replacement_count += 1
            source_occurrences[(docs_href, pinned)].append(relative_document)
            return ('<span class="documentation-unavailable" title="API documentation '
                    'has not been generated for this item">API documentation unavailable</span>'
                    + match.group("separator")
                    + f'<a href="{html.escape(pinned, quote=True)}">Lean source</a>')

        if verified_source_links:
            rendered = _SOURCE_DOCUMENTATION_PAIR_RE.sub(replace_source, rendered)
        if rendered != source:
            temporary = document.with_name(f".{document.name}.tmp")
            temporary.write_text(rendered, encoding="utf-8")
            os.replace(temporary, document)

    entries = [
        {
            "documentation_href": documentation_href,
            "source_pages": sorted(source_pages),
            "verso_href": verso_href,
        }
        for (documentation_href, verso_href), source_pages in sorted(
            occurrences.items()
        )
    ]
    manifest: dict[str, object] = {
        "entries": entries,
        "policy": "missing-api-page-with-valid-verso-fallback",
        "replacement_count": replacement_count,
        "schema_version": 1,
    }
    if verified_source_links:
        manifest["policy"] = "missing-api-page-with-verified-reading-or-source-fallback"
        entries.extend({"documentation_href": docs, "source_href": pinned,
                        "source_pages": sorted(pages), "fallback_kind": "pinned-git-source"}
                       for (docs, pinned), pages in sorted(source_occurrences.items()))
    (site_root / _UNAVAILABLE_DOCUMENTATION_MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def write_route_aliases(root: Path, project: dict[str, object]) -> None:
    """Materialize the stable navigation routes emitted by the Verso navbar.

    Older branch builders store book content as ``<slug>/chapNN/...`` (or
    ``books/<slug>/chapNN/...``), while the shared navbar deliberately links
    to ``books/<slug>/chapters/chapNN/...``.  Static hosts do not provide a
    rewrite layer, so publish tiny redirect pages for every generated route.
    The same mismatch exists for paper ``sectionNN`` routes.
    """

    kind = str(project["kind"])
    slug = str(project["slug"])
    destination = root / kind / slug
    candidates = [root / slug, destination]
    source = best_dir(candidates)
    if source is None:
        return

    mappings: list[tuple[Path, Path]] = []
    if kind == "books":
        book = source / "book"
        if has_index(book):
            mappings.append((book, destination / "book"))
        for chapter in sorted(source.iterdir()):
            if chapter.is_dir() and re.fullmatch(r"chap\d+", chapter.name):
                mappings.append((chapter, destination / "chapters" / chapter.name))
    elif kind == "papers":
        for section in sorted(source.iterdir()):
            if section.is_dir() and re.fullmatch(
                r"section\d+(?:_part\d+)?", section.name
            ):
                mappings.append((section, destination / "sections" / section.name))

    for source_tree, alias_tree in mappings:
        # Snapshot the source indexes before creating aliases; on v4.26 the
        # source and destination share a parent directory.
        indexes = list(source_tree.rglob("index.html"))
        for source_index in indexes:
            relative = source_index.parent.relative_to(source_tree)
            alias_dir = alias_tree / relative
            alias_index = alias_dir / "index.html"
            if alias_index.is_file() or alias_index == source_index:
                continue
            target = Path(os.path.relpath(source_index.parent, alias_dir)).as_posix()
            if target == ".":
                continue
            write_redirect(alias_index, target.rstrip("/") + "/", "Open page")


def versioned_doc_entry(
    src_root: Path,
    project: dict[str, object],
) -> Path | None:
    """Find one project entry inside its untouched versioned doc-gen tree."""

    branch = str(project.get("branch", "")).strip()
    if not branch:
        return None
    kind = str(project["kind"])
    kind_title = str(project["kindTitle"])
    name = str(project["name"])
    leaf = "Book.html" if kind == "books" else "Paper.html"
    roots = (
        src_root / "versions" / branch / "docs" / "ReasBook",
        src_root / "versions" / branch / "docs",
    )
    for root in roots:
        for candidate in (
            root / kind_title / name / leaf,
            root / name / leaf,
            root / f"{name}.html",
        ):
            if candidate.is_file():
                return candidate
    return None


def html_page(
    title: str,
    links: list[tuple[str, str]],
    back_href: str,
    *,
    stylesheet: str,
    home_href: str,
    eyebrow: str = "Library Index",
) -> str:
    escaped_title = html.escape(title)
    items = "\n".join(
        "\n".join(
            [
                "      <li>",
                f'        <a class="resource-link" href="{html.escape(href, quote=True)}">',
                f"          <span>{html.escape(label)}</span>",
                '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                "        </a>",
                "      </li>",
            ]
        )
        for href, label in links
    )
    if not items:
        items = '      <li class="empty-state">No published resources yet.</li>'
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head(title, stylesheet),
            "<body>",
            *masthead(home_href),
            '  <main id="main-content" class="page-shell narrow-shell">',
            '    <section class="page-heading">',
            f'      <p class="eyebrow">{html.escape(eyebrow)}</p>',
            f"      <h1>{escaped_title}</h1>",
            "    </section>",
            '    <ul class="resource-list" role="list">',
            items,
            "    </ul>",
            f'    <a class="back-link" href="{html.escape(back_href, quote=True)}">'
            '<span aria-hidden="true">&#8592;</span> Back to ReasBook</a>',
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def project_page(
    project: dict[str, str],
    links: list[tuple[str, str]],
    *,
    has_versions: bool,
) -> str:
    name = project["name"]
    kind = project["kindTitle"].rstrip("s")
    branch = project.get("branch", "")
    title = display_name(name)
    items = "\n".join(
        "\n".join(
            [
                "      <li>",
                f'        <a class="resource-link" href="{html.escape(href, quote=True)}">',
                f"          <span>{html.escape(label)}</span>",
                '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                "        </a>",
                "      </li>",
            ]
        )
        for href, label in links
    )
    if not items:
        items = '      <li class="empty-state">No published resources yet.</li>'
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head(title, "../../static/catalog.css"),
            "<body>",
            *masthead("../../", "../../versions/" if has_versions else None),
            '  <main id="main-content" class="page-shell narrow-shell">',
            '    <nav class="breadcrumb" aria-label="Breadcrumb">',
            '      <a href="../../">ReasBook</a><span aria-hidden="true">/</span>',
            f"      <span>{html.escape(project['kindTitle'])}</span>",
            "    </nav>",
            '    <section class="page-heading project-heading">',
            f'      <p class="eyebrow">{html.escape(kind)} &middot; '
            f'<span translate="no">{html.escape(branch)}</span></p>',
            f"      <h1>{html.escape(title)}</h1>",
            f'      <code class="identifier" translate="no">{html.escape(name)}</code>',
            "    </section>",
            '    <ul class="resource-list" role="list">',
            items,
            "    </ul>",
            '    <a class="back-link" href="../../"><span aria-hidden="true">&#8592;</span> '
            "Back to ReasBook</a>",
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def catalog_page(projects: list[dict[str, str]], *, has_versions: bool) -> str:
    groups: list[str] = []
    for kind, heading in (("books", "Books"), ("papers", "Papers")):
        rows = sorted(
            (project for project in projects if project["kind"] == kind),
            key=lambda project: project["name"].lower(),
        )
        if not rows:
            continue
        links = []
        for project in rows:
            name = project["name"]
            links.extend(
                [
                    "      <li>",
                    f'        <a class="catalog-row" href="./sites/{html.escape(project["slug"], quote=True)}/">',
                    '          <span class="catalog-title">',
                    f"            <strong>{html.escape(display_name(name))}</strong>",
                    f'            <code translate="no">{html.escape(name)}</code>',
                    "          </span>",
                    '          <span class="catalog-version" translate="no">'
                    f"{html.escape(project.get('branch', ''))}</span>",
                    '          <span class="link-arrow" aria-hidden="true">&#8594;</span>',
                    "        </a>",
                    "      </li>",
                ]
            )
        groups.extend(
            [
                '    <section class="catalog-group">',
                '      <div class="group-heading">',
                f"        <h2>{heading}</h2>",
                f'        <span class="group-count">{len(rows)}</span>',
                "      </div>",
                '      <ul class="catalog-list" role="list">',
                *links,
                "      </ul>",
                "    </section>",
            ]
        )
    if not groups:
        groups = ['    <p class="empty-state">No published books or papers yet.</p>']
    versions_href = "./versions/" if has_versions else None
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            *page_head("ReasBook", "./static/catalog.css"),
            "<body>",
            *masthead("./", versions_href),
            '  <main id="main-content" class="page-shell">',
            '    <section class="catalog-intro">',
            '      <p class="eyebrow">Lean Library Index</p>',
            "      <h1>ReasBook</h1>",
            "      <p>Books and papers formalized in Lean.</p>",
            "    </section>",
            *groups,
            "  </main>",
            '  <footer class="site-footer"><span>ReasBook</span><span>Formal Mathematics</span></footer>',
            "</body>",
            "</html>",
            "",
        ]
    )


def write_catalog_asset(dst_root: Path) -> None:
    source = ASSETS_DIR / "catalog.css"
    if not source.is_file():
        raise FileNotFoundError(f"missing catalog stylesheet: {source}")
    static = dst_root / "static"
    static.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, static / "catalog.css")


def main() -> None:
    projects = json.loads(os.environ["PROJECTS_JSON"])
    src_root = Path(".artifacts/monolith")
    dst_root = Path(".site")

    if dst_root.exists():
        shutil.rmtree(dst_root)
    if src_root.exists():
        shutil.copytree(src_root, dst_root)
    else:
        dst_root.mkdir(parents=True)
    write_catalog_asset(dst_root)
    has_versions = (dst_root / "versions" / "index.html").is_file()

    route_roots = [dst_root]
    versions_root = dst_root / "versions"
    if versions_root.is_dir():
        route_roots.extend(
            path for path in sorted(versions_root.iterdir()) if path.is_dir()
        )
    for route_root in route_roots:
        for project in projects:
            write_route_aliases(route_root, project)

    # Rebuild the docs tree canonically instead of merging several layouts.
    docs_root = dst_root / "docs"
    if docs_root.exists():
        shutil.rmtree(docs_root)
    docs_reasbook = docs_root / "ReasBook"
    (docs_reasbook / "Books").mkdir(parents=True, exist_ok=True)
    (docs_reasbook / "Papers").mkdir(parents=True, exist_ok=True)

    sites_root = dst_root / "sites"
    if sites_root.exists():
        shutil.rmtree(sites_root)
    sites_root.mkdir(parents=True, exist_ok=True)

    book_links: list[tuple[str, str]] = []
    paper_links: list[tuple[str, str]] = []

    for project in projects:
        slug = project["slug"]
        kind = project["kind"]
        kind_title = project["kindTitle"]
        name = project["name"]
        leaf = "Book.html" if kind == "books" else "Paper.html"

        docs_candidates = [
            src_root / "docs" / "ReasBook" / kind_title / name,
            src_root / "docs" / "ReasBook" / name,
            src_root / "docs" / kind_title / name,
            src_root / "docs" / name,
        ]
        docs_src = best_dir(docs_candidates)
        docs_file_candidates = (
            src_root / "docs" / "ReasBook" / kind_title / name / leaf,
            src_root / "docs" / "ReasBook" / name / leaf,
            src_root / "docs" / kind_title / name / leaf,
            src_root / "docs" / name / leaf,
            src_root / "docs" / "ReasBook" / f"{name}.html",
            src_root / "docs" / f"{name}.html",
        )
        docs_file = next(
            (candidate for candidate in docs_file_candidates if candidate.is_file()),
            None,
        )
        canonical_docs = docs_reasbook / kind_title / name
        preserved_doc = versioned_doc_entry(src_root, project)
        if preserved_doc is not None:
            published_doc = dst_root / preserved_doc.relative_to(src_root)
            relative_target = Path(
                os.path.relpath(published_doc, canonical_docs)
            ).as_posix()
            write_redirect(
                canonical_docs / leaf,
                relative_target,
                f"Open {display_name(name)} Documentation",
            )
        elif docs_src is not None:
            shutil.copytree(docs_src, canonical_docs)
            canonical_leaf = canonical_docs / leaf
            if not canonical_leaf.is_file():
                root_page_candidates = [
                    src_root / "docs" / "ReasBook" / f"{name}.html",
                    src_root / "docs" / f"{name}.html",
                ]
                root_page = next(
                    (
                        candidate
                        for candidate in root_page_candidates
                        if candidate.is_file()
                    ),
                    None,
                )
                if root_page is not None:
                    shutil.copy2(root_page, canonical_leaf)
        elif docs_file is not None:
            # Explicit Lake ``roots`` projects can emit only a root HTML file
            # (for example ``docs/ReasBook/TR_LALM_theory.html``) rather than
            # a directory named after the project. Normalize that file into
            # the canonical kind/project/leaf layout.
            canonical_docs.mkdir(parents=True, exist_ok=True)
            shutil.copy2(docs_file, canonical_docs / leaf)

        if canonical_docs.is_dir() and (canonical_docs / leaf).is_file():
            write_docs_index(
                canonical_docs,
                leaf,
                stylesheet="../../../../static/catalog.css",
            )

        pages_candidates = [
            src_root / kind / slug,
            src_root / slug,
        ]

        site_dir = sites_root / slug
        site_dir.mkdir(parents=True, exist_ok=True)

        site_nav: list[tuple[str, str]] = []
        if any(candidate.is_dir() for candidate in pages_candidates):
            build_pages_tree(pages_candidates, site_dir / "pages")
            site_nav.append(("./pages/", "Pages"))
        if canonical_docs.is_dir():
            site_docs = site_dir / "docs"
            site_docs.mkdir()
            canonical_target = Path(
                os.path.relpath(canonical_docs / leaf, site_docs)
            ).as_posix()
            write_redirect(
                site_docs / leaf,
                canonical_target,
                f"Open {display_name(name)} Documentation",
            )
            write_docs_index(
                site_docs,
                leaf,
                stylesheet="../../../static/catalog.css",
            )
            site_nav.append(("./docs/", "Documentation"))

        map_dir = dst_root / "theorem-maps" / kind / slug
        if map_dir.is_dir():
            site_nav.append((f"../../theorem-maps/{kind}/{slug}/", "Theorem Map"))

        project_page_data = {str(key): str(value) for key, value in project.items()}
        (site_dir / "index.html").write_text(
            project_page(
                project_page_data,
                site_nav,
                has_versions=has_versions,
            ),
            encoding="utf-8",
        )

        if canonical_docs.is_dir():
            if kind == "books":
                book_links.append((f"./Books/{name}/", name))
            else:
                paper_links.append((f"./Papers/{name}/", name))

    # Documentation index pages point at the canonical ReasBook/<Kind>/ tree.
    (docs_reasbook / "index.html").write_text(
        "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                *page_head("ReasBook Documentation", "../../static/catalog.css"),
                "<body>",
                *masthead("../../", "../../versions/" if has_versions else None),
                '  <main id="main-content" class="page-shell narrow-shell">',
                '    <section class="page-heading">',
                '      <p class="eyebrow">API Reference</p>',
                "      <h1>Documentation</h1>",
                "    </section>",
                "    <h2>Books</h2>",
                '    <ul class="resource-list" role="list">',
                *[
                    f'      <li><a class="resource-link" href="{html.escape(href, quote=True)}"><span>{html.escape(display_name(label))}</span><span class="link-arrow" aria-hidden="true">&#8594;</span></a></li>'
                    for href, label in sorted(book_links)
                ],
                "    </ul>",
                "    <h2>Papers</h2>",
                '    <ul class="resource-list" role="list">',
                *[
                    f'      <li><a class="resource-link" href="{html.escape(href, quote=True)}"><span>{html.escape(display_name(label))}</span><span class="link-arrow" aria-hidden="true">&#8594;</span></a></li>'
                    for href, label in sorted(paper_links)
                ],
                "  </main>",
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )
    (docs_root / "index.html").write_text(
        html_page(
            "Documentation",
            [("./ReasBook/", "Browse API Documentation")],
            "../",
            stylesheet="../static/catalog.css",
            home_href="../",
            eyebrow="Reference",
        ),
        encoding="utf-8",
    )

    # Root site index is the project catalog, regardless of whether a Verso
    # branch previously produced a root index.html.
    (dst_root / "index.html").write_text(
        catalog_page(projects, has_versions=has_versions),
        encoding="utf-8",
    )

    documentation_audit = reconcile_documentation_links(dst_root)
    unavailable = int(documentation_audit["replacement_count"])
    if unavailable:
        print(
            "Marked "
            f"{unavailable} generated Documentation link(s) as unavailable; "
            f"see {_UNAVAILABLE_DOCUMENTATION_MANIFEST}"
        )

    # The README is the public catalog. Keep old catalog URLs as redirects,
    # while preserving all per-project Docs and Verso routes and assets.
    write_reader_entrypoints(dst_root)


if __name__ == "__main__":
    main()
