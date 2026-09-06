#!/usr/bin/env python3
"""Generate ChapXX.lean aggregation files for books that have ChapXX/ directories
but no sectionXX.lean files.  Each ChapXX.lean imports all .lean files in the
corresponding chapter directory.

Usage:  python3 scripts/generate_chapter_aggregates.py [--book <BookName> ...]
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

CHAPTER_RE = re.compile(r"^(?:chap)(\d+)$", re.IGNORECASE)
BOOK_TITLES = {
    "AlgebraicTopology_May_1999": "A Concise Course in Algebraic Topology (May, 1999)",
    "CombinatorialGroupTheory_Magnus_2004": "Combinatorial Group Theory (Magnus, Karrass, Solitar, 2004)",
    "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017": "Convex Analysis and Monotone Operator Theory (Bauschke & Combettes, 2017)",
    "FirstOrderMethodsOptimization_Beck_2017": "First-Order Methods in Optimization (Beck, 2017)",
    "RiemannSurfaces_Forster_1981": "Lectures on Riemann Surfaces (Forster, 1981)",
}


def generate_chapter_aggregate(book_dir: Path, book_name: str, chap_dir: Path) -> bool:
    """Generate a ChapXX.lean file for the given chapter directory.

    Returns True if the file was written (changed), False if unchanged.
    """
    chap_name = chap_dir.name  # e.g., "Chap01"
    chap_num = int(CHAPTER_RE.match(chap_name).group(1))

    items = sorted(
        [p for p in chap_dir.iterdir() if p.suffix == ".lean"],
        key=lambda p: p.stem.lower(),
    )

    if not items:
        return False

    lines = ["import Mathlib"]
    for item in items:
        # Skip if the item is a subdirectory (like Theorem_10_72/Index.lean)
        # These are handled by the parent .lean file
        parts = item.relative_to(book_dir).parts
        mod = ".".join(part.replace(".lean", "") for part in parts)
        lines.append(f"import {book_name}.{mod}")

    book_title = BOOK_TITLES.get(book_name, book_name)
    lines.append("")
    lines.append("/-!")
    lines.append(f"# Chapter {chap_num:02d} — {book_title}")
    lines.append("")
    lines.append(f"Aggregation module for all formalized items in Chapter {chap_num}.")
    lines.append("-/")

    content = "\n".join(lines) + "\n"
    chap_lean = book_dir / f"{chap_name}.lean"

    try:
        old = chap_lean.read_text(encoding="utf-8")
    except FileNotFoundError:
        old = None

    if old == content:
        return False

    chap_lean.write_text(content, encoding="utf-8")
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate ChapXX.lean aggregation files")
    parser.add_argument(
        "--book", dest="books", action="append", default=[],
        help="Only process the given book(s). Repeat for multiple books.  "
             "Default: all books with ChapXX/ directories.",
    )
    parser.add_argument(
        "--books-root", default="ReasBook/Books",
        help="Path to the Books directory (default: ReasBook/Books)",
    )
    args = parser.parse_args()

    books_root = Path(args.books_root)
    if not books_root.is_dir():
        raise SystemExit(f"Books root not found: {books_root}")

    target_books = set(args.books) if args.books else None

    total_written = 0
    total_chapters = 0

    for book_dir in sorted(books_root.iterdir()):
        if not book_dir.is_dir():
            continue
        book_name = book_dir.name
        if target_books and book_name not in target_books:
            continue

        # Find chapter directories
        chap_dirs = sorted(
            [d for d in book_dir.iterdir() if d.is_dir() and CHAPTER_RE.match(d.name)],
            key=lambda d: d.name,
        )

        if not chap_dirs:
            continue

        print(f"--- {book_name} ({len(chap_dirs)} chapters) ---")
        for chap_dir in chap_dirs:
            written = generate_chapter_aggregate(book_dir, book_name, chap_dir)
            total_chapters += 1
            if written:
                total_written += 1
                print(f"  Wrote {chap_dir.name}.lean")
            else:
                print(f"  {chap_dir.name}.lean (unchanged)")

    print(f"\nProcessed {total_chapters} chapters, wrote {total_written} files")


if __name__ == "__main__":
    main()