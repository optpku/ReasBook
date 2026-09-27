#!/usr/bin/env python3
"""Retire aggregate catalog pages without touching project reading content."""

from __future__ import annotations

import argparse
import html
from pathlib import Path
import re


README_URL = "https://github.com/optpku/ReasBook#readme"


def redirect_page(target: str = README_URL) -> str:
    target = html.escape(target, quote=True)
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
            "  <title>ReasBook README</title>",
            "</head>",
            "<body>",
            '  <main id="main-content">',
            f'    <p><a href="{target}">Open ReasBook README</a></p>',
            "  </main>",
            "</body>",
            "</html>",
            "",
        ]
    )


def write_reader_entrypoints(site: Path) -> list[Path]:
    """Replace only known catalog indexes; preserve Docs/Verso descendants.

    Old bookmarks remain usable, but the GitHub README is the only public
    aggregate catalog. This is navigation policy, not access control.
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
        indexes.update((root / "sites").glob("*/index.html"))

    content = redirect_page()
    for path in sorted(indexes):
        if path.is_symlink() or site not in path.resolve().parents:
            raise ValueError(f"catalog index must be inside the site: {path}")
        path.write_text(content, encoding="utf-8")
    return sorted(indexes)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    args = parser.parse_args()
    paths = write_reader_entrypoints(args.site)
    print(f"Redirected {len(paths)} catalog indexes to the GitHub README")


if __name__ == "__main__":
    main()
