#!/usr/bin/env python3
"""Publish direct, existence-checked static reader entry points."""

from __future__ import annotations

import argparse
import html
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

COMMON_SOURCE = Path(__file__).resolve().parents[2] / "sdk" / "common" / "src"
if str(COMMON_SOURCE) not in sys.path:
    sys.path.insert(0, str(COMMON_SOURCE))

from reasbook_sdk_common.catalog import catalog_page  # noqa: E402


README_URL = "https://github.com/optpku/ReasBook#readme"


def reading_target(path: Path, site: Path) -> Path | None:
    """Follow local legacy refreshes without sending the reader through them."""
    visited: set[Path] = set()
    while path not in visited:
        visited.add(path)
        if path.is_symlink() or not path.is_file() or site not in path.resolve().parents:
            return None
        text = path.read_text(encoding="utf-8")
        match = re.search(r'<meta\b[^>]*http-equiv=[\"\']refresh[\"\'][^>]*'
                          r'content=[\"\'][^;]*;\s*url=([^\"\']+)', text, re.IGNORECASE)
        if not match:
            return path
        url = urlsplit(html.unescape(match.group(1)))
        # Absolute public URLs are not filesystem paths in this projection.
        if url.scheme or url.netloc or url.path.startswith('/'):
            return path if url.path.startswith('/') and not url.netloc else None
        path = (path.parent / unquote(url.path)).resolve()
        if path.is_dir():
            path /= "index.html"
    return None


def project_entries(root: Path, site: Path) -> list[tuple[str, Path]]:
    found: dict[str, tuple[str, Path]] = {}
    for pattern in ('sites/*', 'projects/*', 'books/*', 'papers/*'):
        for project in sorted(root.glob(pattern)):
            if not project.is_dir() or project.is_symlink() or project.name in found:
                continue
            for relative in (('pages/index.html', 'docs/index.html')
                             if project.parent.name == 'sites' else ('index.html',)):
                target = reading_target(project / relative, site)
                if target is None:
                    continue
                text = target.read_text(encoding="utf-8")
                title = re.search(r'<title[^>]*>(.*?)</title>', text, re.DOTALL | re.IGNORECASE)
                label = html.unescape(re.sub('<[^>]+>', '', title.group(1))).strip().removesuffix(' -- ReasBook') if title else project.name
                found[project.name] = (label, target)
                break
    return list(found.values())


def redirect_page(target: str = README_URL, *, title: str = "ReasBook README") -> str:
    target = html.escape(target, quote=True)
    title = html.escape(title)
    return "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            "<head>",
            '  <meta charset="utf-8" />',
            '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
            '  <meta name="robots" content="noindex,follow" />',
            f'  <meta http-equiv="refresh" content="0; url={target}" />',
            f'  <link rel="canonical" href="{target}" />',
            f"  <title>{title}</title>",
            "</head>",
            "<body>",
            '  <main id="main-content">',
            f'    <p><a href="{target}">Open {title}</a></p>',
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def write_reader_entrypoints(site: Path) -> list[Path]:
    """Keep aggregate visitors on the static site; preserve content descendants."""
    site = site.resolve()
    if not site.is_dir():
        raise ValueError(f"site directory does not exist: {site}")
    roots = [site]
    versions = site / "versions"
    if versions.is_dir():
        roots.extend(
            path for path in sorted(versions.iterdir())
            if path.is_dir() and not path.is_symlink()
            and re.fullmatch(r"v\d+\.\d+\.\d+", path.name)
        )

    indexes: set[Path] = {site / "index.html"}
    project_indexes: set[Path] = set()
    for root in roots:
        for relative in (
            "index.html", "books/index.html", "papers/index.html",
            "sites/index.html", "versions/index.html", "docs/index.html",
            "docs/ReasBook/index.html", "docs/ReasBook/Books/index.html",
            "docs/ReasBook/Papers/index.html", "theorem-maps/index.html",
        ):
            path = root / relative
            if path.is_file():
                indexes.add(path)
        project_indexes.update((root / "sites").glob("*/index.html"))

    entries_by_root = {root: project_entries(root, site) for root in roots}
    if not entries_by_root[site]:
        entries_by_root[site] = [entry for root in roots[1:] for entry in entries_by_root[root]]
    indexes.update(project_indexes)
    for path in sorted(indexes):
        if path.is_symlink() or site not in path.resolve().parents:
            raise ValueError(f"catalog index must be inside the site: {path}")
        root = next((root for root in reversed(roots) if root in path.parents), site)
        entries = [(label, Path(os.path.relpath(target, path.parent)).as_posix())
                   for label, target in entries_by_root[root]]
        content = catalog_page('ReasBook — Statements and Documentation', entries)
        if path in project_indexes:
            for kind in ("pages", "docs"):
                entry = path.parent / kind / "index.html"
                if (entry.is_file() and not entry.is_symlink()
                        and site in entry.resolve().parents):
                    target = reading_target(entry, site)
                    if target is None:
                        continue
                    content = redirect_page(Path(os.path.relpath(target, path.parent)).as_posix(),
                                            title="project documentation")
                    break
        path.write_text(content, encoding="utf-8")
    return sorted(indexes)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    args = parser.parse_args()
    paths = write_reader_entrypoints(args.site)
    print(f"Updated {len(paths)} catalog and project reading entry points")


if __name__ == "__main__":
    main()
