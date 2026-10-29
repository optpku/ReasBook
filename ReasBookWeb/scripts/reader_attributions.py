#!/usr/bin/env python3
"""Add source author bylines to full literate Verso pages after rendering.

Ordinary Lean header comments are intentionally absent from Verso's document
AST. This narrow, build-time step adds metadata below the page title without
rewriting native highlighted terms, hover data, anchors, or mathematical prose.
"""

from __future__ import annotations

import argparse
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import tempfile
from urllib.parse import urlsplit


BEGIN = "<!-- BEGIN REASBOOK SOURCE ATTRIBUTION -->"
END = "<!-- END REASBOOK SOURCE ATTRIBUTION -->"
FIELDS = {"authors", "scope", "provenance", "evidence_url", "source_url"}


class TitlePosition(HTMLParser):
    def __init__(self, source: str):
        super().__init__(convert_charrefs=False)
        self.source = source
        self.lines = [0]
        for line in source.splitlines(keepends=True):
            self.lines.append(self.lines[-1] + len(line))
        self.stack: list[tuple[str, bool]] = []
        self.position: int | None = None

    def handle_starttag(self, tag, attrs):
        if tag in {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}:
            return
        data = dict(attrs)
        in_main = (bool(self.stack and self.stack[-1][1])
                   or "main" in (data.get("class") or "").split()
                   or data.get("id") == "main-content")
        self.stack.append((tag, in_main))

    def handle_startendtag(self, tag, attrs):
        pass

    def handle_endtag(self, tag):
        if tag == "h1" and self.stack and self.stack[-1][1] and self.position is None:
            line, column = self.getpos()
            start = self.lines[line - 1] + column
            self.position = self.source.index(">", start) + 1
        for index in range(len(self.stack) - 1, -1, -1):
            if self.stack[index][0] == tag:
                del self.stack[index:]
                break


def attribution_html(credit: dict[str, str]) -> str:
    if set(credit) != FIELDS or not all(isinstance(value, str) for value in credit.values()):
        raise ValueError("invalid source attribution record")
    if credit["scope"] not in {"file", "chapter", "project"}:
        raise ValueError("invalid source attribution scope")
    label = ("Lean authors" if credit["scope"] == "file" else
             f'Lean contributors ({credit["scope"]}-level attribution)')
    body = (f'<div class="reader-attribution"><p>{label}: '
            f'{html.escape(credit["authors"] or "not recorded")}.</p>')
    links = []
    for field, text in (("source_url", "Source header"), ("evidence_url", "Attribution source")):
        if url := credit[field]:
            parsed = urlsplit(url)
            if parsed.scheme != "https" or parsed.netloc != "github.com":
                raise ValueError("source attribution links must be HTTPS GitHub URLs")
            title = f' title="{html.escape(credit["provenance"], quote=True)}"' if field == "evidence_url" else ""
            links.append(f'<a href="{html.escape(url, quote=True)}"{title}>{text}</a>')
    if credit["provenance"] and not credit["evidence_url"]:
        links.append(html.escape(credit["provenance"]))
    if links:
        body += '<p>' + ' · '.join(links) + '</p>'
    return BEGIN + body + '</div>' + END


def annotate_page(source: str, credit: dict[str, str]) -> str:
    block = attribution_html(credit)
    if BEGIN in source or END in source:
        if source.count(BEGIN) != 1 or source.count(END) != 1 or source.index(BEGIN) > source.index(END):
            raise ValueError("ambiguous source attribution markers")
        return source[:source.index(BEGIN)] + block + source[source.index(END) + len(END):]
    parser = TitlePosition(source)
    parser.feed(source)
    parser.close()
    if parser.position is None:
        raise ValueError("full literate page is missing its main content title")
    return source[:parser.position] + block + source[parser.position:]


def apply_attributions(site: Path, manifest: Path) -> int:
    if site.is_symlink() or not site.is_dir() or manifest.is_symlink():
        raise ValueError("unsafe attribution input")
    site = site.resolve()
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1 or not isinstance(payload.get("pages"), dict):
        raise ValueError("invalid reader attribution manifest")
    changes = []
    for route, credit in payload["pages"].items():
        if (not isinstance(route, str) or not route or route.startswith("/")
                or "\\" in route or any(part in {".", ".."} for part in route.split("/"))):
            raise ValueError(f"unsafe attribution route: {route!r}")
        page = site / route / "index.html"
        if (not page.is_file() or any(path.is_symlink() for path in (page, *page.parents))
                or site not in page.resolve().parents):
            raise ValueError(f"missing or unsafe attributed page: {route}")
        previous = page.read_text(encoding="utf-8")
        content = annotate_page(previous, credit)
        if content != previous:
            changes.append((page, content))
    # Validate every target before changing any output. Atomic replacement of
    # each page also makes retries safe after a failed/interrupted build.
    for page, content in changes:
        descriptor, name = tempfile.mkstemp(dir=page.parent, prefix=".attribution-", suffix=".tmp")
        temporary = Path(name)
        try:
            os.fchmod(descriptor, page.stat().st_mode & 0o777)
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                handle.write(content)
            os.replace(temporary, page)
        finally:
            temporary.unlink(missing_ok=True)
    return len(payload["pages"])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    count = apply_attributions(args.site, args.manifest)
    print(f"Verified source attribution on {count} full literate pages")


if __name__ == "__main__":
    main()
