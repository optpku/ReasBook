#!/usr/bin/env python3
"""Preserve imported notices and apply confirmed first-party project headers."""
from __future__ import annotations

import argparse
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parents[1]
PROVENANCE = (
    "TropicalFatFish/ReasBook-integer-programming@"
    "cd8690514e91159fccb6bfdf14ab167259196471:"
    "ReasBook/Books/IntegerProgramming_Conforti_2014/README.md "
    "(Confirmed formalization attribution)."
)
HEADER = (
    "/-\n"
    "Authors: Ziyu Wang\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Project-level attribution: " + PROVENANCE + "\n"
    "Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.\n"
    "-/\n\n"
)


def ordinary_comment_end(source: str, start: int) -> int | None:
    """Return the end of a nested ordinary comment, preserving its exact text."""
    if not source.startswith("/-", start) or source.startswith(("/--", "/-!"), start):
        return None
    depth = 0
    for match in re.finditer(r"/-|-/", source[start:]):
        depth += 1 if match[0] == "/-" else -1
        if depth == 0:
            return start + match.end()
    raise ValueError("Unterminated opening comment")


def has_authors(header: str) -> bool:
    return bool(re.search(r"(?m)^[ \t]*Authors:[ \t]*\S", header))


def with_header(source: str, path: Path) -> str:
    stripped = source.lstrip()
    end = ordinary_comment_end(stripped, 0)
    if end is not None and has_authors(stripped[:end]):
        return source
    module = re.match(r"module[ \t]*\r?\n\s*", stripped)
    if module:
        end = ordinary_comment_end(stripped, module.end())
        if end is not None and has_authors(stripped[module.end():end]):
            # Keep all upstream copyright/author/license fields exactly as supplied.
            return stripped[module.end():end] + "\n\nmodule\n\n" + stripped[end:].lstrip("\r\n")
    if path.name == "DPRM.lean" or "DPRM" in path.relative_to(PROJECT).parts:
        raise ValueError(f"Refusing to infer missing upstream attribution: {path}")
    return HEADER + source


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Report required changes without writing.")
    args = parser.parse_args()
    changed = 0
    for path in sorted(PROJECT.rglob("*.lean")):
        if any(part in {".lake", ".git", ".venv"} for part in path.relative_to(PROJECT).parts):
            continue
        source = path.read_text(encoding="utf-8")
        updated = with_header(source, path)
        if updated == source:
            continue
        changed += 1
        if not args.check:
            path.write_text(updated, encoding="utf-8")
    print(f"Lean headers: {changed} file(s) {'need updating' if args.check else 'updated'}.")
    return int(args.check and changed > 0)


if __name__ == "__main__":
    raise SystemExit(main())
