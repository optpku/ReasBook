"""Read the literal data in template-based curated maps without executing JS."""

from __future__ import annotations

from html.parser import HTMLParser
import json
from pathlib import Path
import re


_JS_PART = re.compile(
    r""""(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*'|`(?:[^`\\]|\\.)*`|/\*[\s\S]*?\*/|//[^\r\n]*"""
)


def _literal_items(script: str) -> list:
    masked = _JS_PART.sub(lambda match: " " * len(match[0]), script)
    assignments = list(re.finditer(r"\b(?:var|let|const)\s+ITEMS\s*=\s*(\[)", masked))
    if len(assignments) != 1 or len(re.findall(r"\bITEMS\s*=", masked)) != 1:
        raise ValueError("missing or ambiguous literal curated items")
    start = assignments[0].start(1)
    depth = 0
    end = None
    for position in range(start, len(masked)):
        if masked[position] == "[":
            depth += 1
        elif masked[position] == "]":
            depth -= 1
            if depth == 0:
                end = position + 1
                break
    if end is None or not masked[end:].lstrip().startswith(";"):
        raise ValueError("curated items must be a complete literal assignment")
    literal = script[start:end]
    chunks = []
    position = 0
    for match in _JS_PART.finditer(literal):
        chunks.append(
            re.sub(
                r"([,{]\s*)([A-Za-z_$][\w$]*)\s*:",
                r'\1"\2":',
                literal[position : match.start()],
            )
        )
        chunks.append(" " if match[0].startswith(("//", "/*")) else match[0])
        position = match.end()
    chunks.append(
        re.sub(r"([,{]\s*)([A-Za-z_$][\w$]*)\s*:", r'\1"\2":', literal[position:])
    )
    value = json.loads("".join(chunks))
    if not isinstance(value, list) or not value:
        raise ValueError("no published curated graph statements")
    return value


class _Templates(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.app = False
        self.templates = []
        self.inert_depth = 0
        self.counts = {}
        self.statements = set()

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        script_type = (attributes.get("type") or "").strip().lower()
        if (
            tag == "script"
            and not self.templates
            and not self.inert_depth
            and attributes.get("src") in {"app.js", "./app.js"}
            and script_type
            in {"", "text/javascript", "application/javascript", "module"}
        ):
            self.app = True
        if tag in {"noscript", "iframe", "object"}:
            self.inert_depth += 1
        if tag == "template":
            identifier = attributes.get("id", "")
            self.counts[identifier] = self.counts.get(identifier, 0) + 1
            self.templates.append((identifier, []))

    def handle_data(self, value):
        if self.templates and not self.inert_depth:
            self.templates[-1][1].append(value)

    def handle_endtag(self, tag):
        if tag in {"noscript", "iframe", "object"}:
            self.inert_depth = max(0, self.inert_depth - 1)
        if tag == "template" and self.templates:
            identifier, text = self.templates.pop()
            if "".join(text).strip():
                self.statements.add(identifier)


def validate_curated_map(directory: Path, project) -> None:
    files = {
        name: directory / name for name in ("metadata.json", "app.js", "index.html")
    }
    if any(path.is_symlink() or not path.is_file() for path in files.values()):
        raise ValueError("missing curated graph files")
    metadata = json.loads(files["metadata.json"].read_text(encoding="utf-8"))
    context = metadata.get("project", {})
    if metadata.get("generation", {}).get("mode") != "curated-static" or (
        context.get("id"),
        context.get("kind"),
        context.get("branch"),
        context.get("commit"),
        context.get("sourceRoot", "").rstrip("/"),
    ) != (
        project.project_id,
        project.kind,
        project.branch,
        project.commit,
        project.source_path.rstrip("/"),
    ):
        raise ValueError("curated graph identity or format mismatch")
    items = _literal_items(files["app.js"].read_text(encoding="utf-8"))
    ids = [item.get("id") for item in items if isinstance(item, dict)]
    if (
        len(ids) != len(items)
        or any(not isinstance(value, str) or not value for value in ids)
        or len(set(ids)) != len(ids)
    ):
        raise ValueError("invalid curated graph statement ids")
    edges = 0
    for item in items:
        dependencies = item.get("dependencies")
        if (
            not isinstance(dependencies, list)
            or any(not isinstance(dep, str) or dep not in ids for dep in dependencies)
            or len(set(dependencies)) != len(dependencies)
        ):
            raise ValueError("invalid curated graph dependencies")
        edges += len(dependencies)
    if (
        type(metadata.get("nodes")) is not int
        or type(metadata.get("edges")) is not int
        or metadata["nodes"] != len(items)
        or metadata["edges"] != edges
    ):
        raise ValueError("curated graph counts do not match literal data")
    page = _Templates()
    page.feed(files["index.html"].read_text(encoding="utf-8"))
    if not page.app or any(
        "statement-" + value not in page.statements
        or page.counts.get("statement-" + value) != 1
        for value in ids
    ):
        raise ValueError(
            "curated graph has no active app or readable statement templates"
        )
