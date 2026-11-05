"""Share repeated Verso head assets without rewriting mathematical content."""
from __future__ import annotations

from collections import Counter
from bisect import bisect_right
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
_HTML_TAG = re.compile(
    r'''</?([A-Za-z][A-Za-z0-9:_-]*)(?=[\s/>])(?:[^"'<>]|"[^"]*"|'[^']*')*>'''
)
_VOID_TAGS = frozenset({
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link",
    "meta", "param", "source", "track", "wbr",
})


class _ClassOpening(HTMLParser):
    def __init__(self):
        super().__init__()
        self.values: list[set[str]] = []

    def handle_starttag(self, tag, attrs):
        self.values = [set((value or "").split()) for key, value in attrs if key == "class"]


def _lean_markup_ranges(parts: list[str]) -> tuple[list[int], list[int], list[tuple[int, int, int, int, int]]]:
    """Find real diagnostic containers without parsing native token contents.

    Only real class attributes activate a range. Nested elements of the same
    name extend it; comments and raw scripts/styles cannot close it. Preserve
    an unmatched container through EOF. False positives retain more markup.
    """
    starts: list[int] = []
    ends: list[int] = []
    blocks: list[tuple[int, int, int, int, int]] = []
    code_depth = 0
    code_begin = None
    active = None
    depth = offset = beginning = 0
    for index, part in enumerate(parts):
        if index % 2 == 0:
            for match in _HTML_TAG.finditer(part):
                name = match.group(1).lower()
                opening = match.group(0)
                closing = opening.startswith("</")
                if name == "code":
                    if not closing:
                        if code_depth == 0:
                            code_begin = (index, match.start(), match.end())
                        code_depth += 1
                    elif code_depth:
                        code_depth -= 1
                        if code_depth == 0 and code_begin is not None:
                            block_index, block_start, content_start = code_begin
                            # Raw blocks/comments or malformed nesting inside
                            # code retain the entire outer code block unchanged.
                            if block_index == index:
                                blocks.append((index, block_start, content_start,
                                               match.start(), match.end()))
                if active is not None:
                    if name == active:
                        depth += -1 if closing else 1
                        if depth == 0:
                            starts.append(beginning)
                            ends.append(offset + match.end())
                            active = None
                elif not closing and ("has-info" in opening or "&" in opening):
                    parser = _ClassOpening()
                    parser.feed(opening)
                    if any("has-info" in value for value in parser.values):
                        beginning = offset + match.start()
                        if name in _VOID_TAGS:
                            starts.append(beginning)
                            ends.append(offset + match.end())
                        else:
                            active, depth = name, 1
        offset += len(part)
    if active is not None:
        starts.append(beginning)
        ends.append(offset)
    return starts, ends, blocks


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

    Keep complete code blocks that overlap diagnostic containers unchanged.
    Other blocks retain every token, binding/hover attribute and source text.
    Inter-text under `.has-info` can carry a diagnostic underline and must
    retain its wrapper; a diagnostic elsewhere does not affect a clean block.
    """
    whitespace = re.compile(r"""<span class=(?:"inter-text"|'inter-text'|inter-text)>([^<]*)</span>""")
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
        diagnostic_starts, diagnostic_ends, blocks = _lean_markup_ranges(parts)
        count = 0
        offsets = []
        offset = 0
        for part in parts:
            offsets.append(offset)
            offset += len(part)
        edits: dict[int, list[tuple[int, int, str]]] = {}
        for index, start, content_start, content_end, end in blocks:
            position = bisect_right(diagnostic_ends, offsets[index] + start)
            if (position < len(diagnostic_starts)
                    and diagnostic_starts[position] < offsets[index] + end):
                continue
            part = parts[index]
            parser = _ClassOpening()
            parser.feed(part[start:content_start])
            if len(parser.values) != 1 or not {"hl", "lean", "block"}.issubset(parser.values[0]):
                continue
            result, n = whitespace.subn(r"\1", part[content_start:content_end])
            count += n
            if n:
                edits.setdefault(index, []).append((content_start, content_end, result))
        for index, changes in edits.items():
            part = parts[index]
            chunks = []
            position = 0
            for start, end, replacement in changes:
                chunks.extend([part[position:start], replacement])
                position = end
            chunks.append(part[position:])
            parts[index] = "".join(chunks)
        result = "".join(parts)
        if result != source:
            atomic_write_text(path, result)
            changed += 1
            saved += len(source.encode()) - len(result.encode())
            wrappers += count
    return {"pages": changed, "saved_bytes": saved, "wrappers": wrappers}
