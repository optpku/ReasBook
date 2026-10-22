#!/usr/bin/env python3
"""Check per-file Lean authorship without inferring or rewriting author names."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable


HEADER_SCRIPTS = str(Path(__file__).resolve().parents[2] / "ReasBookWeb" / "scripts")
if HEADER_SCRIPTS not in sys.path:
    sys.path.insert(0, HEADER_SCRIPTS)
from lean_headers import author_field, opening_header as opening_header  # noqa: E402


_PLACEHOLDER = re.compile(
    r"(?i)(?:\b(?:todo|tbd|unknown|anonymous|none)\b|[<>?]|"
    r"\b(?:contributors|maintainers|your name|author name|not provided)\b)"
)
_TOOL_LABELS = {"codex", "openai codex", "chatgpt", "claude", "claude code", "github copilot"}


def author_error(source: str) -> str | None:
    header = opening_header(source)
    if header is None:
        return "missing opening ordinary author header"
    try:
        authors = author_field(header)
    except ValueError as error:
        return str(error)
    if authors is None:
        return "missing nonempty Authors: line in opening header"
    if not authors or any(not name.strip() for name in authors.split(",")):
        return "empty author name"
    names = [name.strip() for name in authors.split(",")]
    if _PLACEHOLDER.search(authors) or any(name.casefold() in _TOOL_LABELS for name in names):
        return "placeholder or generic team label instead of verified code authors"
    if any(not any(character.isalpha() for character in name) for name in names):
        return "author name must contain letters, not just punctuation or digits"
    if authors.endswith("."):
        return "author list must not end with a period"
    return None


def _git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), *args])


def lean_sources(
    repo: Path, *, ref: str | None = None, paths: Iterable[str] = ()
) -> Iterable[tuple[str, str]]:
    """Read a Git tree, or tracked and non-ignored first-party working source."""
    selected = tuple(paths)
    if ref is not None:
        names = _git(repo, "ls-tree", "-r", "--name-only", "-z", ref, "--", *selected)
    else:
        names = _git(
            repo, "ls-files", "-z", "--cached", "--others", "--exclude-standard",
            "--", *selected,
        )
    for raw in sorted(set(names.split(b"\0")) - {b""}):
        name = raw.decode("utf-8")
        parts = Path(name).parts
        if not name.endswith(".lean") or any(
            part in {".lake", ".git", ".work", ".venv", "node_modules"}
            for part in parts
        ):
            continue
        path = repo / name
        if ref is None:
            if not path.is_file():
                continue  # A tracked deletion is not published working source.
            source = path.read_text(encoding="utf-8")
        else:
            source = _git(repo, "show", f"{ref}:{name}").decode("utf-8")
        yield name, source


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--ref", help="Audit a Git ref instead of the working tree (read-only).")
    parser.add_argument("--path", action="append", default=[], help="Repeat to restrict source paths.")
    args = parser.parse_args(argv)
    count = failed = 0
    for name, source in lean_sources(args.repo.resolve(), ref=args.ref, paths=args.path):
        count += 1
        error = author_error(source)
        if error:
            print(f"{name}: {error}")
            failed += 1
    print(f"Lean author headers: {count} files checked, {failed} invalid.")
    if count == 0:
        print("No Lean source matched; check the repository/ref/path selection.")
        return 1
    return int(failed > 0)


if __name__ == "__main__":
    raise SystemExit(main())
