"""Sync a standalone copy of this paper while preserving attribution and proofs.

Run with --source /path/to/standalone/lean_project. Only this project's Lean
modules are copied; manuscript files, caches and workspace generators are not.
Existing notices are preserved. A new module must supply its own verified
author notice in the standalone source.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re


PROJECT = "glowinski_admm_counterexample"
DEST = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^(\s*(?:(?:public|private|meta)\s+)*import\s+)([^\n]+)", re.M)
OWNED = re.compile(r"(?<![\w.])(ReasLib|GlowinskiADMM|glowinski_admm_counterexample)(?=\.|\s|$)")


def author_header(text: str) -> str | None:
    """Keep an existing verified notice verbatim, including third-party credit."""
    match = re.match(r"\A\s*/-(?![!-])[\s\S]*?-/(?:\s*\n)?", text)
    return match[0] if match and "Authors:" in match[0] else None


def relocated(text: str) -> str:
    def rewrite(match: re.Match[str]) -> str:
        body, sep, comment = match[2].partition("--")
        return match[1] + OWNED.sub(PROJECT + r".\1", body) + sep + comment
    return IMPORT.sub(rewrite, text).rstrip("\n") + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="Compare without writing files")
    args = parser.parse_args()
    source = args.source.resolve()
    assert source != DEST.resolve(), "Provide the standalone, unprefixed project"
    assert (source / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.0"
    files = sorted([*(source / "ReasLib").rglob("*.lean"),
                    *(source / "GlowinskiADMM").rglob("*.lean"),
                    *(source / name for name in ("ReasLib.lean", "GlowinskiADMM.lean", PROJECT + ".lean"))])
    assert files
    updates = []
    for path in files:
        target = DEST / path.relative_to(source)
        original = path.read_text()
        transformed = relocated(original)
        supplied = author_header(transformed)
        existing = author_header(target.read_text()) if target.exists() else None
        if supplied and existing:
            assert supplied == existing, f"Review differing author notices: {target}"
        if not supplied:
            if existing is None:
                parser.error(f"Missing verified opening Authors: notice in {path}")
            transformed = existing + transformed
        updates.append((target, transformed))
    for target, transformed in updates:
        if args.check:
            assert target.read_text() == transformed, target
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(transformed)
    print(f"PASS: {len(files)} project modules {'match' if args.check else 'synced with'} supplied or existing author headers.")


if __name__ == "__main__":
    main()
