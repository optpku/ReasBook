"""Read Lean file headers; bundled alongside the release's source generator."""

from __future__ import annotations

import re


def header_span(source: str) -> tuple[int, int] | None:
    """Return the opening ordinary comment's exact source offsets."""
    text = source.lstrip("\ufeff \t\r\n")
    start = len(source) - len(text)
    if not text.startswith("/-") or text.startswith(("/-!", "/--")):
        return None
    depth = 1
    for match in re.finditer(r"/-|-/", source[start + 2:]):
        depth += 1 if match.group() == "/-" else -1
        if depth == 0:
            return start, start + 2 + match.end()
    return None


def opening_header(source: str) -> str | None:
    span = header_span(source)
    return source[span[0]:span[1]] if span else None


def outer_header_text(header: str) -> str:
    """Mask nested comment contents; an example inside one is not metadata."""
    chars = list(header)
    depth = 0
    previous = 0
    for match in re.finditer(r"/-|-/", header):
        if depth > 1:
            for index in range(previous, match.start()):
                if chars[index] not in "\r\n":
                    chars[index] = " "
        token = match.group()
        if token == "/-":
            depth += 1
        else:
            depth -= 1
        for index in range(match.start(), match.end()):
            chars[index] = " "
        previous = match.end()
    return "".join(chars)


def author_field(header: str, *, allow_singular: bool = False) -> str | None:
    """Read one outer Authors field, including indented comma continuations."""
    keyword = r"Authors?" if allow_singular else "Authors"
    pattern = re.compile(r"^[ \t]*" + keyword + r":[ \t]*([^\r\n]*)$")
    lines = outer_header_text(header).splitlines()
    fields = [(index, match[1].strip()) for index, line in enumerate(lines)
              if (match := pattern.fullmatch(line))]
    if not fields:
        return None
    if len(fields) != 1:
        raise ValueError("multiple author fields in opening header")
    index, value = fields[0]
    while value.endswith(",") and index + 1 < len(lines):
        index += 1
        continuation = lines[index]
        if not continuation.strip() or not continuation[:1].isspace() or ":" in continuation:
            break
        value += " " + continuation.strip()
    return value
