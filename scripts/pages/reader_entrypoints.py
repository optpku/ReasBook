#!/usr/bin/env python3
"""Retire aggregate catalog pages without touching project reading content."""

from __future__ import annotations

import argparse
import html
from pathlib import Path
import re


README_URL = "https://github.com/optpku/ReasBook#readme"


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
    """Replace only known catalog indexes; preserve Docs/Verso descendants.

    Aggregate catalogs return to the GitHub README. Project bookmarks go
    directly to their existing reading/docs entry, without a catalog round trip.
    """
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

    indexes.update(project_indexes)
    for path in sorted(indexes):
        if path.is_symlink() or site not in path.resolve().parents:
            raise ValueError(f"catalog index must be inside the site: {path}")
        content = redirect_page()
        if path in project_indexes:
            for kind in ("pages", "docs"):
                entry = path.parent / kind / "index.html"
                if (entry.is_file() and not entry.is_symlink()
                        and site in entry.resolve().parents):
                    content = redirect_page(f"./{kind}/", title="project documentation")
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
