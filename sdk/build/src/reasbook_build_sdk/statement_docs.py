"""Source statement excerpts, not proof dumps or reconstructed Lean output."""

from __future__ import annotations

from dataclasses import dataclass
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
from urllib.parse import quote, urldefrag

from .errors import BuildFailed


_IMPORT = re.compile(r"(?m)^[ \t]*(?:public[ \t]+)?import\s+([^\n]+)")
_REFERENCE = re.compile(r"(?m)^[ \t]*(?:recall\b|#check\b)")
_RAW_STRING = re.compile(r'r(#+)?"')
_CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'")
_COMMAND = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?:(?:@\[[^\n]*?\]|private|protected|noncomputable|"
    r"unsafe|partial|public|local|scoped)\s+)*(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|"
    r"constant|structure|class|inductive|instance|example|recall|#check|#print|#eval|"
    r"namespace|section|mutual|end|variable|universe|open|export|include|omit|"
    r"local|scoped|notation|infix[lr]?|prefix|postfix|attribute|set_option|"
    r"syntax|macro|elab|initialize|import|module|prelude)\b"
)
_STATEMENT_KINDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "opaque", "axiom", "constant",
    "structure", "class", "inductive", "instance", "recall", "#check",
})
_CONTEXT_KINDS = frozenset({
    "namespace", "variable", "universe", "open", "include", "omit",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix",
})
_MARKER = 'data-reasbook-statements="true"'
_STYLE = """
.reasbook-statements { margin: 1.5em 0; }
.reasbook-statements pre { white-space: pre-wrap; overflow-wrap: anywhere;
  padding: 1em; border: 1px solid #8886; border-radius: .4em; }
.reasbook-statements .statement-note { font-size: .9em; }
.reasbook-statements li { margin: .4em 0; }
.reasbook-statements .statement-reference { text-decoration: underline;
  text-underline-offset: .15em; }
.reasbook-statements .statement-reference:focus-visible { outline: 2px solid currentColor; }
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
        elif char == "r" and (raw := _RAW_STRING.match(source, index)):
            terminator = '"' + (raw.group(1) or '')
            close = source.find(terminator, raw.end())
            size = len(source) - index if close < 0 else close + len(terminator) - index
        elif char == "'" and (literal := _CHAR_LITERAL.match(source, index)):
            size = literal.end() - index
        elif char == "«":
            close = source.find("»", index + 1)
            size = len(source) - index if close < 0 else close + 1 - index
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


@dataclass(frozen=True)
class Statement:
    """An explicitly labelled, verbatim excerpt; never a checked declaration."""

    signature: str
    prose: str
    context: tuple[str, ...]
    reference: bool
    # The declaration identifier as written, not an elaborated/qualified name.
    name: str = ""
    # Unicode-codepoint offsets into the original source, in display order:
    # active context commands followed by the selected signature. Presentation
    # consumers can slice checked semantic data without re-elaborating a copy.
    source_ranges: tuple[tuple[int, int], ...] = ()


def statement_source_url(source: str, url: str, statement: Statement) -> str:
    """Link the selected signature, not preceding context or a helper command.

    Ranges are Unicode offsets into this exact source. A stale range must not
    silently send the reader to another declaration. The URL's revision is
    preserved; callers must provide source from that revision.
    """
    if not statement.source_ranges:
        raise ValueError("statement has no source range")
    start, stop = statement.source_ranges[-1]
    if not (0 <= start < stop <= len(source)) or source[start:stop] != statement.signature:
        raise ValueError("statement range does not match source")
    first = source.count("\n", 0, start) + 1
    last = source.count("\n", 0, stop - 1) + 1
    fragment = f"L{first}" + (f"-L{last}" if last != first else "")
    return urldefrag(url)[0] + "#" + fragment


def _signature(command: str, kind: str) -> str:
    # Fields and constructors ARE the definition, not an implementation/proof
    # boundary. Keep the entire bounded type command (including field defaults).
    if kind in {"recall", "#check", "structure", "class", "inductive"}:
        return command.strip()
    mask = _code_mask(command)
    depth = 0
    pending_lets = 0
    type_match = False
    for match in re.finditer(r"[()\[\]{}⦃⦄]|:=|\b(?:where|let|letI|match)\b|(?m:^\s*\|)", mask):
        token = match.group().strip()
        if token in {"(", "[", "{", "⦃"}:
            depth += 1
        elif token in {")", "]", "}", "⦄"}:
            depth = max(0, depth - 1)
        elif depth == 0:
            if token in {"let", "letI"}:
                pending_lets += 1
                continue
            if token == "match":
                type_match = True
                continue
            if token == ":=" and pending_lets:
                pending_lets -= 1
                continue
            if token == "|" and type_match:
                continue
            # A short definitional RHS is often the mathematical definition.
            # Never include tactic proofs or a long implementation in previews.
            rhs = mask[match.end():].strip()
            if (token == ":=" and kind in {"def", "abbrev"}
                    and len(command) <= 600 and not re.search(r"\b(by|do)\b", rhs)):
                return command.strip()
            return command[:match.start()].strip()
    return command.strip()


def statement_excerpts(source: str, *, label: str = "") -> tuple[Statement, ...]:
    """Conservative lexical previews of source commands, with proofs omitted.

    This is intentionally not a Lean parser or elaborator. Types are never
    inferred for #check. Commands are bounded by source indentation and known
    command starts; comments/strings are masked before scanning. Documentation
    remains the authoritative elaborated view, and every preview links to source.
    """
    mask = _code_mask(source)
    commands = list(_COMMAND.finditer(mask))
    frames: list[list[tuple[str, int]]] = [[]]
    statements: list[Statement] = []
    comments = list(re.finditer(r"/-(?:!|-)?(.*?)-/", source, re.DOTALL))
    command_end = 0
    for number, match in enumerate(commands):
        if match.start() < command_end:
            continue
        indent = len(match['indent'])
        context_command = match['kind'] in _CONTEXT_KINDS | {
            "section", "mutual", "end", "import", "module", "prelude", "set_option", "attribute",
        }
        end = next((other.start() for other in commands[number + 1:]
                    if len(other['indent']) <= indent or context_command), len(source))
        # Exclude trailing comments belonging to the next command.
        code_end = end
        for comment in reversed(comments):
            if match.end() < comment.start() < code_end and not mask[comment.end():code_end].strip():
                code_end = comment.start()
        raw_command = source[match.start():code_end]
        command_start = match.start() + len(raw_command) - len(raw_command.lstrip())
        command = raw_command.strip()
        kind = match['kind']
        command_end = end
        # A mutual block owns an `end`, but is not namespace/notation context.
        # Keep its frame so closing it cannot discard the enclosing scope.
        if kind in {"namespace", "section", "mutual"}:
            frames.append([])
        if kind == "end":
            if len(frames) > 1:
                frames.pop()
            continue
        if kind in _CONTEXT_KINDS and not re.search(r"\bin\s*$", command):
            frames[-1].append((command, command_start))
        if kind not in _STATEMENT_KINDS or re.search(r"\bprivate\b", mask[match.start():match.start('kind')]):
            continue
        prose = ""
        preceding = next((comment for comment in reversed(comments)
                          if comment.end() <= match.start()), None)
        if preceding and not mask[preceding.end():match.start()].strip():
            prose = preceding.group(1).strip()
            if re.search(r"Authors?:|Copyright|Declarations for this item", prose):
                prose = ""
        signature = _signature(command, kind)
        if signature:
            name = ""
            if kind not in {"instance", "recall", "#check"}:
                identifier = re.match(r"\s+((?:«[^»]+»|[^\s([{:=])+)", source[match.end():])
                if identifier:
                    name = identifier[1]
            context = tuple(item for frame in frames for item in frame)
            ranges = tuple((start, start + len(text)) for text, start in context)
            statements.append(Statement(signature, prose,
                                        tuple(text for text, _ in context),
                                        kind in {"recall", "#check"}, name,
                                        (*ranges, (command_start, command_start + len(signature)))))
    if label:
        # A citation in helper prose is not the item itself. Magnus uses hyphens
        # in numbers; other books use dots, sometimes after a Chapter10 prefix.
        identifier = r"[.-]".join(re.escape(part) for part in
                                  re.split(r"(?<=\d)[.-](?=\d)", label))
        identifier = identifier.replace(r"\ ", r"\s+")
        identifier += r"(?!\d|[.-]\d)"
        heading = re.compile(r"^\s*(?:Chapter\s*\d+\s*[:.,—–-]?\s+)?" + identifier, re.I)
        mention = re.compile(r"(?<![\w.-])" + identifier, re.I)
        def rank(item: Statement) -> tuple[bool, bool, bool]:
            # Numbered headings are stronger evidence than prose vocabulary.
            # "auxiliary objective/state" can be the mathematics being defined;
            # only an explicit Helper/Auxiliary prefix marks a helper comment.
            helper = bool(re.match(r"\s*(?:helpers?|auxiliary)\b", item.prose, re.I))
            return not bool(heading.search(item.prose)), helper, not bool(mention.search(item.prose))
        statements.sort(key=rank)  # Stable: preserve source order within a tier.
    return tuple(statements)


def source_reading(source: str) -> SourceReading:
    mask = _code_mask(source.removeprefix("\ufeff"))
    source = source.removeprefix("\ufeff")
    imports = tuple(name for match in _IMPORT.finditer(mask)
                    for name in match.group(1).split())
    remaining = _IMPORT.sub("", mask)
    remaining = re.sub(r"(?m)^\s*(?:module|prelude)\s*$", "", remaining)
    # Modern facade modules may wrap only imports/comments in `public section`
    # and leave local variables/open commands for documentation. They still
    # have no statement of their own; follow their project imports as contents.
    facade = True
    continuation_indent: int | None = None
    for line in remaining.splitlines():
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        context = re.match(r"\s*(?:(?:public|noncomputable)\s+)?(section|namespace|end|open|universe|variable)\b", line)
        if context and not re.search(r"\bin\s*\S*", line):
            continuation_indent = indent if context[1] in {"variable", "open"} else None
        elif continuation_indent is not None and indent > continuation_indent:
            continue
        else:
            facade = False
            break
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
    return SourceReading(body, imports, bool(_REFERENCE.search(mask)), facade)


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


def _module_order(module: str) -> tuple:
    """Keep chapter groups together, but compare item numbers before kinds."""
    parent, _, leaf = module.rpartition(".")
    numbers = tuple(int(part) for part in re.findall(r"\d+", leaf))
    return _natural(parent), not bool(numbers), numbers, _natural(leaf)


def prose_html(prose: str) -> str:
    """Only inline code markup is supported; all source HTML stays inert."""
    return re.sub(r'`([^`\n]+)`', r'<code>\1</code>', html.escape(prose))


@dataclass(frozen=True, order=True)
class _Reference:
    start: int
    stop: int
    module: str
    name: str


def _compiled_references(source: str, module: str, path: Path | None) -> tuple[_Reference, ...]:
    """Read Lean's resolved constants, not guesses from `open` or short names.

    The caller supplies the .ilean beside the checked module's .olean and binds
    it into the documentation cache identity. Lean 4.26 uses format 4; 4.30+
    uses format 5. Both store zero-based UTF-16 LSP ranges (not UTF-8 offsets).
    Missing/unknown metadata leaves the source text intact without fake links.
    """
    if path is None:
        return ()
    if path.is_symlink() or not path.is_file():
        raise BuildFailed(f"unsafe reference metadata: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise BuildFailed(f"invalid reference metadata: {path}") from exc
    if not isinstance(data, dict) or data.get('module') != module or data.get('version') not in (4, 5):
        return ()
    references = data.get('references')
    if not isinstance(references, dict):
        return ()
    # Lean's LSP character positions count supplementary Unicode characters
    # twice. Only real codepoint boundaries are accepted.
    positions: dict[tuple[int, int], int] = {}
    offset = 0
    # LSP lines end at LF, not at Unicode separators inside Lean strings.
    for row, line in enumerate(source.split('\n')):
        column = 0
        positions[row, column] = offset
        for char in line:
            column += 2 if ord(char) > 0xFFFF else 1
            offset += 1
            positions[row, column] = offset
        offset += 1  # LF; the final row has no following range to map.
    result: set[_Reference] = set()
    for encoded, info in references.items():
        try:
            ident = json.loads(encoded)
        except (TypeError, ValueError):
            continue
        constant = ident.get('c') if isinstance(ident, dict) else None
        if not isinstance(constant, dict) or not isinstance(info, dict):
            continue  # local variables are encoded as `f`, not `c`
        owner, name = constant.get('m'), constant.get('n')
        if not (isinstance(owner, str) and isinstance(name, str) and owner and name
                and all(part and part not in {'.', '..'} for part in owner.split('.'))
                and not any(char in owner for char in '/\\\x00\r\n')
                and not name.startswith('_private.')):
            continue
        usages = info.get('usages', [])
        if not isinstance(usages, list):
            continue
        for location in usages:
            if not (isinstance(location, list) and len(location) in {4, 5}
                    and all(type(n) is int and n >= 0 for n in location[:4])):
                continue
            start = positions.get(tuple(location[:2]))
            stop = positions.get(tuple(location[2:4]))
            if start is None or stop is None or not start < stop:
                continue
            spelling = source[start:stop].removeprefix('_root_.')
            # Reject stale/misaligned ranges and notation expansion ranges.
            # A resolved short name is valid even when an `open` made it short.
            if spelling and (spelling == name or name.endswith('.' + spelling)):
                result.add(_Reference(start, stop, owner, name))
    return tuple(sorted(result))


class _Anchors(HTMLParser):
    def __init__(self, source: str) -> None:
        super().__init__(convert_charrefs=True)
        self.ids: set[str] = set()
        self.stub = False
        self.feed(source)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        if identifier := attributes.get('id'):
            self.ids.add(identifier)
        self.stub |= attributes.get('data-reasbook-doc-stub') == 'true'


def _reference_html(item: Statement, references: tuple[_Reference, ...],
                    page: Path, doc_root: Path, anchors: dict[str, _Anchors]) -> str:
    if not item.reference or not item.source_ranges:
        return html.escape(item.signature)
    start, stop = item.source_ranges[-1]
    candidates = [ref for ref in references if start <= ref.start < ref.stop <= stop]
    # Ambiguous/overlapping semantic ranges must never produce nested links or
    # choose an arbitrary declaration. Leave that part of the source unlinked.
    clean = [ref for index, ref in enumerate(candidates)
             if not any(other.start < ref.stop and ref.start < other.stop
                        for other in candidates[:index] + candidates[index + 1:])]
    output: list[str] = []
    cursor = start
    for ref in clean:
        relative = Path(*ref.module.split('.')).with_suffix('.html')
        target = doc_root / relative
        if ref.module not in anchors:
            safe = (target.is_file() and not target.is_symlink()
                    and doc_root.resolve() in target.resolve().parents)
            anchors[ref.module] = _Anchors(target.read_text(encoding='utf-8') if safe else '')
        probe = anchors[ref.module]
        url = ''
        title = 'Documentation: ' + ref.name
        fragment = '#' + quote(ref.name, safe='')
        if not probe.stub and ref.name in probe.ids:
            url = quote(Path(os.path.relpath(target, page.parent)).as_posix(), safe='/') + fragment
        elif ref.module.split('.')[0] in {'Mathlib', 'Init', 'Std', 'Lean', 'Batteries'}:
            url = 'https://leanprover-community.github.io/mathlib4_docs/' + quote(relative.as_posix(), safe='/') + fragment
            title = 'Upstream documentation (current version): ' + ref.name
        if not url:
            continue  # no empty dependency stubs, unknown-package guesses, or search pages
        output.append(html.escape(item.signature[cursor - start:ref.start - start]))
        output.append(f'<a class="statement-reference" href="{html.escape(url, quote=True)}" '
                      f'title="{html.escape(title, quote=True)}">'
                      f'{html.escape(item.signature[ref.start - start:ref.stop - start])}</a>')
        cursor = ref.stop
    output.append(html.escape(item.signature[cursor - start:]))
    return ''.join(output)


def enrich_documentation(
    doc_root: Path,
    module_sources: tuple[tuple[str, Path], ...],
    module_owners: dict[str, frozenset[str]],
    source_urls: dict[str, str],
    *,
    reference_files: dict[str, Path] | None = None,
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
        source = source_path.read_text(encoding="utf-8")
        reading = source_reading(source)
        # Do not retain a whole book's proofs in memory while planning navigation.
        readings[module] = SourceReading("", reading.imports, reading.references, reading.imports_only)
        probe = _Main(page.read_text(encoding="utf-8"))
        if (statement_excerpts(source) or probe.declarations
                or (not reading.imports_only and "".join(probe.text).strip())):
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
        return sorted(found, key=_module_order)

    changed = 0
    anchors: dict[str, _Anchors] = {}
    for module, page in pages.items():
        original = page.read_text(encoding="utf-8")
        if _MARKER in original:
            continue
        reading = readings[module]
        probe = _Main(original)
        sections: list[str] = []
        if reading.references or (not reading.imports_only and not "".join(probe.text).strip()):
            source = sources[module].read_text(encoding="utf-8")
            references = _compiled_references(source, module, (reference_files or {}).get(module))
            excerpts = statement_excerpts(source)
            if probe.declarations:
                excerpts = tuple(item for item in excerpts if item.reference)
            if excerpts:
                sections.extend([
                '<h2 id="reasbook-statements">Statements</h2>',
                '<p class="statement-note">Source excerpts; proofs omitted. '
                '<code>recall</code> restates an existing declaration; '
                '<code>#check</code> records an expression, not its inferred type.</p>',
                ])
            elif not probe.declarations and not "".join(probe.text).strip():
                sections.append('<p>No statement preview is available for this module. See the Lean source.</p>')
            for item in excerpts:
                if item.prose:
                    sections.append(f'<p>{prose_html(item.prose)}</p>')
                signature = _reference_html(item, references, page, doc_root, anchors)
                sections.append(f'<pre><code class="language-lean">{signature}</code></pre>')
                if url := source_urls.get(module):
                    if url != "#":
                        target = statement_source_url(source, url, item)
                        sections.append(f'<p><a href="{html.escape(target, quote=True)}">Lean source</a></p>')
                if item.context:
                    context = html.escape('\n'.join(item.context))
                    sections.append(f'<details><summary>Source context</summary><pre>{context}</pre></details>')
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
            sections.append(f'<p><a href="{html.escape(url, quote=True)}">Module source</a></p>')
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
