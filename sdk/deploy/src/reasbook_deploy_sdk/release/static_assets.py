"""Share repeated Verso head assets without rewriting mathematical content."""
from __future__ import annotations

from collections import Counter
import hashlib
import html
from html.parser import HTMLParser
from pathlib import Path
import re

from reasbook_sdk_common import atomic_write_text

_LIMIT = 8 * 1024 * 1024
_HEAD_CHUNK = 64 * 1024
_CONTEXT_SENSITIVE = re.compile(
    r"document\s*\.\s*currentScript|\bimport\s*\(|\bimport\s*\.\s*meta|"
    r"sourceMappingURL", re.I
)

_CSS_CONTEXT_SENSITIVE = re.compile(r"\burl\s*\(|@import", re.I)


_INERT_CONTAINER = re.compile(r"<(?:template|noscript|textarea)\b", re.I)
_RAW_BLOCK = re.compile(r"<!--.*?-->|<(?P<rawtag>script|style)\b.*?</(?P=rawtag)\s*>", re.I | re.S)


def _protected_parts(text: str) -> list[str]:
    """Alternate editable HTML and exact, correctly matched raw-text blocks."""
    parts = []
    position = 0
    for match in _RAW_BLOCK.finditer(text):
        parts.extend([text[position:match.start()], match.group(0)])
        position = match.end()
    parts.append(text[position:])
    return parts


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
            if (len(content) >= 256 and not _CONTEXT_SENSITIVE.search(content)
                    and not (tag == "style" and _CSS_CONTEXT_SENSITIVE.search(content))):
                self.blocks.append((start, self.text.index(">", end) + 1, tag, content))
            self.active = None
        if tag in {"template", "noscript"}:
            self.hidden = max(0, self.hidden - 1)
        if tag == "head":
            self.in_head = False
            self.closed = True


def _head(path: Path) -> _Head | None:
    # Only head assets are candidates. Do not parse huge Lean expression bodies.
    prefix = bytearray()
    end = None
    with path.open("rb") as stream:
        while len(prefix) < _LIMIT:
            chunk = stream.read(min(_HEAD_CHUNK, _LIMIT - len(prefix)))
            if not chunk:
                break
            prefix.extend(chunk)
            end = re.search(rb"</head\s*>", prefix, re.I)
            if end is not None:
                break
    if end is None or b"__versoSiteRoot" not in prefix[:end.end()]:
        return None
    try:
        text = bytes(prefix[:end.end()]).decode("utf-8")
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
        if _INERT_CONTAINER.search(original):
            continue
        parts = _protected_parts(original)
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


def compact_verso_intertext(site: Path) -> dict[str, int]:
    """Remove unstyled whitespace wrappers inside native Lean code only.

    Keep diagnostic documents, all tokens, binding/hover attributes, source text,
    prose, and scripts/styles unchanged. Inter-text under `.has-info` can carry
    a diagnostic underline and must retain its wrapper.
    """
    codes = re.compile(r"(<code\b[^>]*>)(.*?)(</code\s*>)", re.I | re.S)
    class CodeOpening(HTMLParser):
        def __init__(self):
            super().__init__()
            self.classes = set()
        def handle_starttag(self, tag, attrs):
            if tag == "code":
                self.classes = set((dict(attrs).get("class") or "").split())
    whitespace = re.compile(r"""<span class=(?:"inter-text"|'inter-text'|inter-text)>([^<]*)</span>""")
    diagnostic = re.compile(r"""<[^>]*\bclass\s*=\s*(?:"[^"]*\bhas-info\b[^"]*"|'[^']*\bhas-info\b[^']*'|has-info(?:\s|>))""", re.I)
    changed = saved = wrappers = 0
    for path in sorted(Path(site).rglob("*.html")):
        if "docs" in path.relative_to(site).parts:
            continue
        source = path.read_text(encoding="utf-8")
        if "__versoSiteRoot" not in source or "inter-text" not in source:
            continue
        if _INERT_CONTAINER.search(source):
            continue
        parts = _protected_parts(source)
        if any(diagnostic.search(part) for part in parts[::2]):
            continue
        count = 0
        def rewrite(match):
            nonlocal count
            opening, content, closing = match.groups()
            parser = CodeOpening()
            parser.feed(opening)
            tokens = parser.classes
            if not {"hl", "lean", "block"}.issubset(tokens) or "has-info" in content or "has-info" in tokens:
                return match.group(0)
            result, n = whitespace.subn(r"\1", content)
            count += n
            return opening + result + closing
        for i in range(0, len(parts), 2):
            parts[i] = codes.sub(rewrite, parts[i])
        result = "".join(parts)
        if result != source:
            atomic_write_text(path, result)
            changed += 1
            saved += len(source.encode()) - len(result.encode())
            wrappers += count
    return {"pages": changed, "saved_bytes": saved, "wrappers": wrappers}
