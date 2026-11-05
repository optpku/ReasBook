"""Share repeated Verso head assets without rewriting mathematical content."""
from __future__ import annotations

from collections import Counter
from bisect import bisect_right
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import parse_qs, quote, unquote, urljoin, urlsplit

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
_HTML_ATTRIBUTE = re.compile(
    r'''([^\s"'<>/=]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?'''
)

_DOCUMENTATION_NAV_STYLE = """
/* ReasBook readable module navigation */
.nav .module_list, .nav .module_list details { min-width: 0; }
.nav .nav_file { display: block; box-sizing: border-box; max-width: 100%;
  white-space: normal; overflow-wrap: anywhere; }
.nav .nav_file a, .nav .nav_link { white-space: normal; overflow-wrap: anywhere; }
"""


def improve_documentation_navigation(site: Path) -> dict[str, int]:
    """Keep full module names readable without widening the page or hiding text."""
    changed = 0
    for path in Path(site).rglob('style.css'):
        if path.is_symlink() or 'docs' not in path.relative_to(site).parts:
            continue
        content = path.read_text(encoding='utf-8')
        if '.nav_file' in content and '.module_list' in content and _DOCUMENTATION_NAV_STYLE not in content:
            atomic_write_text(path, content.rstrip() + '\n' + _DOCUMENTATION_NAV_STYLE)
            changed += 1
    return {'stylesheets': changed}


class _ClassOpening(HTMLParser):
    def __init__(self):
        super().__init__()
        self.values: list[set[str]] = []

    def handle_starttag(self, tag, attrs):
        self.values = [set((value or "").split()) for key, value in attrs if key == "class"]


class _DeclarationAnchors(HTMLParser):
    def __init__(self, source: str):
        super().__init__(convert_charrefs=True)
        self.ids: set[str] = set()
        self.stub = False
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if values.get('id'):
            self.ids.add(values['id'])
        self.stub |= values.get('data-reasbook-doc-stub') == 'true'


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
        self.base_href: str | None = None
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
        hrefs = [value for key, value in attrs if key == 'href']
        if tag == 'base' and self.in_head and not self.hidden and self.base_href is None and hrefs:
            self.base_href = hrefs[0] or ''
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
            tag = binding.sub(lambda m: ('data-b' if not m.group(1) else
                              'data-b="' + handles.get(html.unescape(m.group(1)), m.group(1)) + '"'), tag)
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


def resolve_native_documentation_links(site: Path, base_path: str) -> dict[str, int]:
    """Resolve native constants against the published declaration index.

    Project-local declarations get their actual doc-gen target. Constants absent
    from the bounded project index use mathlib's exact-name finder, explicitly
    labeled as current upstream documentation, rather than a local 404 page.
    Native token/hover markup and raw script/style contents are untouched.
    """
    site = Path(site).resolve()
    indexes: dict[Path, dict] = {}
    target_anchors: dict[Path, set[str]] = {}
    pages = local = upstream = 0
    for page in sorted(site.rglob('*.html')):
        if 'docs' in page.relative_to(site).parts or page.is_symlink():
            continue
        head = _head(page)
        if head is None or head.base_href is None:
            continue
        base = urlsplit(urljoin('https://reasbook.invalid' + base_path + page.relative_to(site).as_posix(), head.base_href))
        if (base.netloc != 'reasbook.invalid' or base.query or base.fragment
                or not re.fullmatch(re.escape(base_path) + r'versions/v[0-9.]+/', base.path)):
            continue
        doc_root = site / base.path[len(base_path):] / 'docs/ReasBook'
        index = doc_root / 'declarations/declaration-data.bmp'
        if doc_root not in indexes:
            if index.is_symlink() or not index.is_file():
                continue
            payload = json.loads(index.read_text(encoding='utf-8'))
            indexes[doc_root] = payload.get('declarations', {})
        declarations = indexes[doc_root]
        source = page.read_text(encoding='utf-8')
        parts = _protected_parts(source)

        def rewrite_link(match):
            nonlocal local, upstream
            tag = match.group(0)
            if match.group(1).lower() != 'a' or tag.startswith('</'):
                return tag
            attributes = list(_HTML_ATTRIBUTE.finditer(tag, match.end(1) - match.start(), len(tag) - 1))
            hrefs = [a for a in attributes if a.group(1).lower() == 'href']
            titles = [a for a in attributes if a.group(1).lower() == 'title']
            if len(hrefs) != 1 or len(titles) != 1:
                return tag
            def value(attr):
                return next((v for v in attr.groups()[1:] if v is not None), '')
            if html.unescape(value(titles[0])) != 'Documentation':
                return tag
            href = urlsplit(urljoin(base.geturl(), html.unescape(value(hrefs[0]))))
            if (href.netloc != 'reasbook.invalid'
                    or href.path.rstrip('/') != base.path + 'docs/ReasBook/find'):
                return tag
            query = parse_qs(href.query)
            if set(query) != {'pattern'} or len(query['pattern']) != 1:
                return tag
            name = query['pattern'][0]
            if not name or any(c in name for c in '\x00\r\n'):
                return tag
            entry = declarations.get(name)
            target_href = entry.get('docLink') if isinstance(entry, dict) else None
            title = 'Documentation'
            if target_href:
                destination = urlsplit(urljoin(base.geturl() + 'docs/ReasBook/', target_href))
                target = (site / unquote(destination.path[len(base_path):])).resolve()
                if (destination.netloc != 'reasbook.invalid' or not destination.path.startswith(base_path)
                        or site not in target.parents or target.is_symlink() or not target.is_file()):
                    return tag
                if target not in target_anchors:
                    probe = _DeclarationAnchors(target.read_text(encoding='utf-8'))
                    target_anchors[target] = set() if probe.stub else probe.ids
                if not destination.fragment or unquote(destination.fragment) not in target_anchors[target]:
                    return tag
                target_href = destination.path + '#' + destination.fragment
                local += 1
            else:
                target_href = 'https://leanprover-community.github.io/mathlib4_docs/find/?pattern=' + quote(name, safe='') + '#doc'
                title = 'Upstream documentation (current version): ' + name
                upstream += 1
            # Replace entire attributes so unquoted and differently quoted input
            # still produces valid, escaped HTML.
            for attribute, replacement in sorted([(hrefs[0], 'href="' + html.escape(target_href, quote=True) + '"'),
                                                    (titles[0], 'title="' + html.escape(title, quote=True) + '"')],
                                                   key=lambda edit: edit[0].start(), reverse=True):
                tag = tag[:attribute.start()] + replacement + tag[attribute.end():]
            return tag

        # _protected_parts keeps executable/raw text exact. Native links have
        # a dedicated title, so ordinary content links do not enter this path.
        for i in range(0, len(parts), 2):
            parts[i] = _HTML_TAG.sub(rewrite_link, parts[i])
        result = ''.join(parts)
        if result != source:
            atomic_write_text(page, result)
            pages += 1
    return {'pages': pages, 'local': local, 'upstream': upstream}


def relativize_native_documentation_links(site: Path, base_path: str) -> dict[str, int]:
    """Shorten native declaration links only when their complete URL is equal."""
    changed = saved = links = 0
    for path in sorted(Path(site).rglob('*.html')):
        if 'docs' in path.relative_to(site).parts:
            continue
        head = _head(path)
        if head is None or head.base_href is None:
            continue
        page_url = 'https://reasbook.invalid' + base_path + path.relative_to(site).as_posix()
        base_url = urljoin(page_url, head.base_href)
        base = urlsplit(base_url)
        if (base.netloc != 'reasbook.invalid' or base.query or base.fragment
                or not re.fullmatch(re.escape(base_path) + r'versions/v[0-9.]+/', base.path)):
            continue
        source = path.read_text(encoding='utf-8')
        if _INERT_CONTAINER.search(source):
            continue
        parts = _protected_parts(source)
        _, _, blocks = _lean_markup_ranges(parts)
        edits: dict[int, list[tuple[int, int, str]]] = {}
        count = 0

        def rewrite_link(match):
            nonlocal count
            if match.group(1).lower() != 'a' or match.group(0).startswith('</'):
                return match.group(0)
            tag = match.group(0)
            start = match.end(1) - match.start()
            attributes = list(_HTML_ATTRIBUTE.finditer(tag, start, len(tag) - 1))
            hrefs = [a for a in attributes if a.group(1).lower() == 'href']
            titles = [a for a in attributes if a.group(1).lower() == 'title']
            if len(hrefs) != 1 or len(titles) != 1:
                return tag
            title = next((v for v in titles[0].groups()[1:] if v is not None), '')
            if html.unescape(title) != 'Documentation':
                return tag
            attribute = hrefs[0]
            group = next((i for i in (2, 3) if attribute.group(i) is not None), None)
            if group is None:
                return tag
            value = attribute.group(group)
            if not value.startswith(base.path + 'docs/'):
                return tag
            relative = value[len(base.path):]
            if urljoin(base_url, html.unescape(relative)) != urljoin(base_url, html.unescape(value)):
                return tag
            count += 1
            return tag[:attribute.start(group)] + relative + tag[attribute.end(group):]

        for index, start, content_start, content_end, end in blocks:
            parser = _ClassOpening()
            parser.feed(parts[index][start:content_start])
            if len(parser.values) != 1 or not {'hl', 'lean', 'block'}.issubset(parser.values[0]):
                continue
            content = parts[index][content_start:content_end]
            compact = _HTML_TAG.sub(rewrite_link, content)
            if compact != content:
                edits.setdefault(index, []).append((content_start, content_end, compact))
        for index, changes in edits.items():
            original, chunks, position = parts[index], [], 0
            for start, end, replacement in changes:
                chunks.extend([original[position:start], replacement])
                position = end
            chunks.append(original[position:])
            parts[index] = ''.join(chunks)
        result = ''.join(parts)
        if result != source:
            atomic_write_text(path, result)
            changed += 1
            links += count
            saved += len(source.encode()) - len(result.encode())
    return {'pages': changed, 'links': links, 'saved_bytes': saved}


def deduplicate_theorem_map_runtime(site: Path, base_path: str) -> dict[str, int]:
    """Share a pinned standalone Viz build verified to render after relocation.

    Unknown distributions remain at their original locations. The actual
    runtime, including its complete third-party notices, stays byte-identical.
    """
    digest = '2e4fe91072268d06387a7b91d7ba11db9a235280df764d49399519faa5f5368d'
    applications = {
        '04856d2078a6d85256a11ec194db838c26f31ca23666f3cd24b812e5cf19a0f3',  # Current SDK app; relocated Viz covered by browser canary.
        '39b8a52288092cc0e9b40c3d4445dab7d71a8dc28bee033ab53a0a286ec5ad41',
        'ba7d9b5219e591e5018467b079de9538aade4c39d49bb800c10adede25ae9c28',
        'a839b931d5d63ded7a05c64346c3fade4f736dddfa5413b9723493dd196d6cdb',
        '9f06f9f9c1899766128bdb07ab6db71a956f3ddb14115055f6cd2313cd4dc2dc',
    }
    root = Path(site)
    candidates = []
    literal = 'script.src = "./vendor/viz-global.js";'
    for runtime in sorted(root.glob('versions/*/theorem-maps/**/vendor/viz-global.js')):
        app = runtime.parent.parent / 'app.js'
        if runtime.is_symlink() or app.is_symlink() or not app.is_file():
            continue
        source = runtime.read_bytes()
        script_bytes = app.read_bytes()
        script = script_bytes.decode('utf-8')
        if (hashlib.sha256(source).hexdigest() == digest
                and hashlib.sha256(script_bytes).hexdigest() in applications
                and script.count(literal) == 1):
            candidates.append((runtime, app, source, script))
    if len(candidates) < 2:
        return {'runtimes': 0, 'saved_bytes': 0}
    relative = Path('static/shared-theorem-maps') / (digest + '.js')
    shared = root / relative
    shared.parent.mkdir(parents=True, exist_ok=True)
    if shared.exists() and (shared.is_symlink() or shared.read_bytes() != candidates[0][2]):
        raise ValueError('shared theorem-map runtime collision')
    shared.write_bytes(candidates[0][2])
    replacement = 'script.src = ' + json.dumps(base_path + relative.as_posix()) + ';'
    saved = -shared.stat().st_size
    for runtime, app, source, script in candidates:
        updated = script.replace(literal, replacement)
        app.write_text(updated, encoding='utf-8')
        runtime.unlink()
        saved += len(source) + len(script.encode()) - len(updated.encode())
    return {'runtimes': len(candidates), 'saved_bytes': saved}
