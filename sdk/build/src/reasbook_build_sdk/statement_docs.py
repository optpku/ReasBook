"""Readable source statements and direct contents for project documentation.

``recall`` and ``#check`` do not introduce declarations for doc-gen4 to render.
Keep their original source, including local notation and variable context, in
the module page. This is source evidence, not a reconstruction of Lean's output.
"""

from __future__ import annotations

from dataclasses import dataclass
import html
from html.parser import HTMLParser
import os
from pathlib import Path
import re
from urllib.parse import quote

from .errors import BuildFailed


_IMPORT = re.compile(r"(?m)^[ \t]*(?:public[ \t]+)?import\s+([^\n]+)")
_REFERENCE = re.compile(r"(?m)^[ \t]*(?:recall\b|#check\b)")
_MARKER = 'data-reasbook-statements="true"'
_STYLE = """
.reasbook-statements { margin: 1.5em 0; }
.reasbook-statements pre { white-space: pre-wrap; overflow-wrap: anywhere;
  padding: 1em; border: 1px solid #8886; border-radius: .4em; }
.reasbook-statements .statement-note { font-size: .9em; }
.reasbook-statements li { margin: .4em 0; }
"""


def _code_mask(source: str) -> str:
    """Blank nested comments and strings without moving offsets or newlines."""
    result = list(source)
    index = 0
    depth = 0
    string = False
    line_comment = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        size = 1
        hidden = True
        if line_comment:
            if char == "\n":
                line_comment = False
        elif depth:
            if pair == "/-":
                depth += 1
                size = 2
            elif pair == "-/":
                depth -= 1
                size = 2
        elif string:
            if char == "\\":
                size = 2
            elif char == '"':
                string = False
        elif pair == "--":
            line_comment = True
            size = 2
        elif pair == "/-":
            depth = 1
            size = 2
        elif char == '"':
            string = True
        else:
            hidden = False
        if hidden:
            for offset in range(index, min(index + size, len(source))):
                if source[offset] != "\n":
                    result[offset] = " "
        index += size
    return "".join(result)


@dataclass(frozen=True)
class SourceReading:
    body: str
    imports: tuple[str, ...]
    references: bool
    imports_only: bool


def source_reading(source: str) -> SourceReading:
    mask = _code_mask(source.removeprefix("\ufeff"))
    source = source.removeprefix("\ufeff")
    imports = tuple(name for match in _IMPORT.finditer(mask)
                    for name in match.group(1).split())
    remaining = _IMPORT.sub("", mask)
    remaining = re.sub(r"(?m)^\s*(?:module|prelude)\s*$", "", remaining)
    # Drop only the file header/import prefix. Subsequent comments, namespaces,
    # variables, notation and multiline expressions retain their exact spelling.
    prefix_end = 0
    for match in _IMPORT.finditer(mask):
        prefix_end = match.end()
    body = source[prefix_end:].strip()
    body = re.sub(
        r"(?m)^-- Declarations for this item will be appended below by the statement pipeline\.\s*",
        "", body,
    ).strip()
    return SourceReading(body, imports, bool(_REFERENCE.search(mask)), not remaining.strip())


class _Main(HTMLParser):
    def __init__(self, source: str) -> None:
        super().__init__(convert_charrefs=True)
        self.offsets = [0] + [match.end() for match in re.finditer("\n", source)]
        self.start: int | None = None
        self.end: int | None = None
        self.text: list[str] = []
        self.declarations = False
        self.feed(source)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "main" and self.start is None:
            line, column = self.getpos()
            self.start = self.offsets[line - 1] + column + len(self.get_starttag_text() or "")
        if self.start is not None and self.end is None:
            classes = (dict(attrs).get("class") or "").split()
            self.declarations |= "decl" in classes

    def handle_endtag(self, tag: str) -> None:
        if tag == "main" and self.start is not None and self.end is None:
            line, column = self.getpos()
            self.end = self.offsets[line - 1] + column

    def handle_data(self, data: str) -> None:
        if self.start is not None and self.end is None:
            self.text.append(data)


def _natural(value: str) -> tuple[tuple[int, object], ...]:
    return tuple((0, int(part)) if part.isdigit() else (1, part.casefold())
                 for part in re.split(r"(\d+)", value))


def module_label(module: str) -> str:
    leaf = module.rsplit(".", 1)[-1]
    leaf = re.sub(r"(?<=\d)_(?=\d)", ".", leaf)
    return leaf.replace("_", " ")


def enrich_documentation(
    doc_root: Path,
    module_sources: tuple[tuple[str, Path], ...],
    module_owners: dict[str, frozenset[str]],
    source_urls: dict[str, str],
) -> int:
    """Enrich a fresh, private doc-gen stage; preserve declarations and anchors.

    Only imports-only modules become contents pages. Their links skip other
    import aggregators and empty leaves, stay within the selected project,
    and point directly at pages with statements. No redirect or URL is removed.
    """
    readings: dict[str, SourceReading] = {}
    sources = dict(module_sources)
    pages: dict[str, Path] = {}
    content_modules: set[str] = set()
    for module, source_path in module_sources:
        page = doc_root / Path(*module.split(".")).with_suffix(".html")
        if page.is_symlink() or not page.is_file() or doc_root.resolve() not in page.resolve().parents:
            raise BuildFailed(f"unsafe or missing statement documentation page: {page}")
        pages[module] = page
        reading = source_reading(source_path.read_text(encoding="utf-8"))
        # Do not retain a whole book's proofs in memory while planning navigation.
        readings[module] = SourceReading("", reading.imports, reading.references, reading.imports_only)
        probe = _Main(page.read_text(encoding="utf-8"))
        if reading.references or probe.declarations or not reading.imports_only:
            content_modules.add(module)

    def leaves(module: str) -> list[str]:
        found: set[str] = set()
        visited = {module}
        pending = list(readings[module].imports)
        while pending:
            child = pending.pop()
            if child in visited or child not in readings:
                continue
            visited.add(child)
            if not (module_owners.get(module, frozenset()) & module_owners.get(child, frozenset())):
                continue
            if child in content_modules:
                found.add(child)
            else:
                pending.extend(readings[child].imports)
        return sorted(found, key=_natural)

    changed = 0
    for module, page in pages.items():
        original = page.read_text(encoding="utf-8")
        if _MARKER in original:
            continue
        reading = readings[module]
        probe = _Main(original)
        sections: list[str] = []
        if reading.references or (not reading.imports_only and not "".join(probe.text).strip()):
            body = source_reading(sources[module].read_text(encoding="utf-8")).body
            sections.extend([
                '<h2 id="reasbook-statements">Statements</h2>',
                '<p class="statement-note">From the Lean source, with its mathematical '
                'comments and local context. <code>recall</code> restates an existing '
                'declaration; <code>#check</code> records a checked expression, '
                'not a new theorem.</p>',
                f'<pre><code class="language-lean">{html.escape(body)}</code></pre>',
            ])
        elif reading.imports_only:
            children = leaves(module)
            sections.append('<h2 id="reasbook-statements">Statements</h2>')
            if children:
                previous_group: str | None = None
                prefix = module.rsplit(".", 1)[0] + "."
                for child in children:
                    target = Path(os.path.relpath(pages[child], page.parent)).as_posix()
                    relative = child.removeprefix(prefix)
                    group = relative.rsplit(".", 1)[0] if "." in relative else ""
                    if group != previous_group:
                        if previous_group is not None:
                            sections.append('</ul>')
                        if group:
                            heading = re.sub(r"\bChap0*(\d+)", r"Chapter \1", group)
                            sections.append(f'<h3>{html.escape(heading)}</h3>')
                        sections.append('<ul class="statement-contents">')
                        previous_group = group
                    label = module_label(child)
                    sections.append(f'<li><a href="{quote(target, safe="/.")}">'
                                    f'{html.escape(label)}</a></li>')
                sections.append('</ul>')
            else:
                sections.append('<p>No statements are published in this module. '
                                'See the source for its imports.</p>')
        if not sections:
            continue
        url = source_urls.get(module)
        if url and url != "#":
            sections.append(f'<p><a href="{html.escape(url, quote=True)}">Lean source</a></p>')
        block = f'<section class="reasbook-statements" {_MARKER}>' + "\n".join(sections) + '</section>'
        if probe.start is not None:
            offset = probe.start
        else:
            # Simplified renderer/test pages need not have a main element.
            body = re.search(r"<body\b[^>]*>", original, re.IGNORECASE)
            if body is None:
                raise BuildFailed(f"documentation page has no content container: {page}")
            offset = body.end()
        rendered = original[:offset] + block + original[offset:]
        page.write_text(rendered, encoding="utf-8")
        changed += 1
    if changed:
        style = doc_root / "style.css"
        if style.is_symlink() or not style.is_file():
            raise BuildFailed("statement documentation requires a safe style.css")
        with style.open("a", encoding="utf-8") as handle:
            handle.write("\n" + _STYLE)
    return changed
