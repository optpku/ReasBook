"""Share repeated Verso head assets without rewriting mathematical content."""
from __future__ import annotations

from collections import Counter
import hashlib
import html
from html.parser import HTMLParser
from pathlib import Path
import re

from reasbook_sdk_common import atomic_write_text

_LIMIT = 1024 * 1024
_CONTEXT_SENSITIVE = re.compile(
    r"document\s*\.\s*currentScript|\bimport\s*\(|\bimport\s*\.\s*meta|"
    r"sourceMappingURL|\burl\s*\(|@import", re.I
)


class _Head(HTMLParser):
    def __init__(self, text: str):
        super().__init__(convert_charrefs=False)
        self.text = text
        self.lines = [0]
        for match in re.finditer("\n", text):
            self.lines.append(match.end())
        self.in_head = False
        self.closed = False
        self.csp = False
        self.hidden = 0
        self.active: tuple[str, int, int] | None = None
        self.blocks: list[tuple[int, int, str, str]] = []

    def absolute_position(self) -> int:
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        if tag == "head":
            self.in_head = True
        if tag in {"template", "noscript"}:
            self.hidden += 1
        values = dict(attrs)
        if tag == "meta" and (values.get("http-equiv") or "").lower() == "content-security-policy":
            self.csp = True
        if self.in_head and not self.hidden and tag in {"style", "script"} and not attrs:
            start = self.absolute_position()
            self.active = tag, start, start + len(self.get_starttag_text())

    def handle_endtag(self, tag):
        if self.active and self.active[0] == tag:
            _, start, content_start = self.active
            end = self.absolute_position()
            content = self.text[content_start:end]
            if len(content) >= 256 and not _CONTEXT_SENSITIVE.search(content):
                self.blocks.append((start, self.text.index(">", end) + 1, tag, content))
            self.active = None
        if tag in {"template", "noscript"}:
            self.hidden = max(0, self.hidden - 1)
        if tag == "head":
            self.in_head = False
            self.closed = True


def _head(path: Path) -> _Head | None:
    # Only head assets are candidates. Do not parse huge Lean expression bodies.
    with path.open("rb") as stream:
        prefix = stream.read(_LIMIT)
    end = re.search(rb"</head\s*>", prefix, re.I)
    if end is None or b"__versoSiteRoot" not in prefix[:end.end()]:
        return None
    try:
        text = prefix[:end.end()].decode("utf-8")
    except UnicodeDecodeError:
        return None
    parser = _Head(text)
    parser.feed(text)
    return parser if parser.closed and not parser.csp else None


def deduplicate_verso_assets(site: Path, base_path: str) -> dict[str, int]:
    """Modify a private staging tree only; preserve Docs and all body bytes.

    Only repeated attribute-free classic scripts/styles are extracted. Scripts
    remain parser-blocking at their original positions. Relative CSS resources,
    module imports, currentScript, CSP, templates and conditional blocks are
    excluded because moving them could change behavior.
    """
    root = Path(site)
    counts: Counter[tuple[str, str]] = Counter()
    documents = []
    for path in sorted(root.rglob("*.html")):
        if "docs" in path.relative_to(root).parts:
            continue
        if path.is_symlink():
            raise ValueError(f"symlinked Verso page: {path}")
        head = _head(path)
        if head is None:
            continue
        documents.append(path)
        for _, _, tag, content in head.blocks:
            counts[tag, hashlib.sha256(content.encode()).hexdigest()] += 1
    saved = assets = replaced = 0
    written = set()
    for path in documents:
        head = _head(path)
        assert head is not None
        text = head.text
        for start, end, tag, content in reversed(head.blocks):
            digest = hashlib.sha256(content.encode()).hexdigest()
            key = tag, digest
            if counts[key] < 2:
                continue
            suffix = "js" if tag == "script" else "css"
            relative = Path("static/shared-verso") / f"{digest}.{suffix}"
            target = root / relative
            if key not in written:
                if target.exists() and (target.is_symlink() or target.read_text() != content):
                    raise ValueError("shared Verso asset collision")
                atomic_write_text(target, content)
                written.add(key)
                assets += 1
                saved -= len(content.encode())
            url = base_path + relative.as_posix()
            replacement = (f'<script src="{url}"></script>' if tag == "script"
                           else f'<link rel="stylesheet" href="{url}">')
            saved += len(text[start:end].encode()) - len(replacement.encode())
            text = text[:start] + replacement + text[end:]
            replaced += 1
        if text != head.text:
            original = path.read_bytes()
            head_bytes = head.text.encode()
            if not original.startswith(head_bytes):
                raise ValueError("Verso staging tree changed during deduplication")
            # Native highlighted Lean, prose, anchors and body scripts are untouched.
            path.write_bytes(text.encode() + original[len(head_bytes):])
    return {"assets": assets, "replaced_blocks": replaced, "saved_bytes": saved}


def compact_verso_metadata(site: Path, base_path: str) -> dict[str, int]:
    """Shorten opaque syntax-highlighting handles without changing source text.

    Binding handles are used only for equality within a page. Intern them,
    shorten their HTML dataset key, and update the shared highlighting scripts.
    Keep the original scripts for any unmodified consumers. API pages are
    excluded, and scripts/styles are protected from HTML attribute rewriting.
    """
    root = Path(site)
    replacements: dict[str, str] = {}
    for script in sorted(root.glob("static/shared-verso/*.js")):
        content = script.read_text(encoding="utf-8")
        if "data-binding" not in content and "dataset.binding" not in content:
            continue
        updated = re.sub(r"\bdataset\.binding\b", "dataset.b", content.replace("data-binding", "data-b"))
        digest = hashlib.sha256(updated.encode()).hexdigest()
        target = root / "static/shared-verso" / f"{digest}.js"
        if target.exists() and target.read_text() != updated:
            raise ValueError("shared highlighting asset collision")
        if not target.exists():
            atomic_write_text(target, updated)
        replacements[base_path + script.relative_to(root).as_posix()] = (
            base_path + target.relative_to(root).as_posix()
        )
    protected = re.compile(r"(<(?:script|style|textarea|template|noscript)\b.*?</(?:script|style|textarea|template|noscript)\s*>)", re.I | re.S)
    tags = re.compile(r"<[A-Za-z][^>]*>")
    binding = re.compile(r'(?<=\s)data-binding="([^"]*)"')
    quotes = re.compile(r'(?<=\s)(data-b|data-verso-hover|data-lean-context|class)="([A-Za-z0-9_.:-]+)"')
    saved = changed = 0
    for path in sorted(root.rglob("*.html")):
        if "docs" in path.relative_to(root).parts:
            continue
        original = path.read_text(encoding="utf-8")
        if "__versoSiteRoot" not in original or "data-binding=" not in original:
            continue
        parts = protected.split(original)
        values = dict.fromkeys(
            html.unescape(match.group(1))
            for part in parts[::2] for tag in tags.finditer(part)
            for match in binding.finditer(tag.group())
        )
        occupied = set(values)
        handles = {}
        index = 0
        for value in values:
            if not value:
                continue
            while f"b{index:x}" in occupied:
                index += 1
            candidate = f"b{index:x}"
            if len(candidate) < len(value):
                handles[value] = candidate
                occupied.add(candidate)
                index += 1

        def rewrite_tag(match):
            tag = match.group()
            tag = binding.sub(lambda m: 'data-b="' + handles.get(html.unescape(m.group(1)), m.group(1)) + '"', tag)
            return quotes.sub(lambda m: m.group(1) + "=" + m.group(2), tag)

        for index, part in enumerate(parts):
            if index % 2:
                if re.match(r"<script\s*>", part, re.I):
                    part = re.sub(r"\bdataset\.binding\b", "dataset.b", part.replace("data-binding", "data-b"))
                for old, new in replacements.items():
                    part = part.replace(old, new)
            else:
                part = tags.sub(rewrite_tag, part)
            parts[index] = part
        updated = "".join(parts)
        if updated != original:
            path.write_text(updated, encoding="utf-8")
            saved += len(original.encode()) - len(updated.encode())
            changed += 1
    return {"pages": changed, "saved_bytes": saved, "scripts": len(replacements)}
