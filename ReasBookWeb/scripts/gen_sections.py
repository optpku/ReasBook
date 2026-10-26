#!/usr/bin/env python3
"""Generate ReasBookSite/Sections.lean from the current ReasBook module tree."""

from __future__ import annotations

import argparse
from functools import lru_cache
import json
import os
import posixpath
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from lean_headers import author_field, header_span
from statement_previews import ITEM_PREVIEWS
from site_config import (
    PROJECT_FRAGMENT,
    SKIP_MODULES,
    SiteConfig,
    load_site_config,
    project_enabled,
    validate_project_selection,
)

TOOLING_ROOT = Path(__file__).resolve().parents[2]
for sdk_source in (
    TOOLING_ROOT / "sdk" / "common" / "src",
    TOOLING_ROOT / "sdk" / "build" / "src",
):
    value = str(sdk_source)
    if value not in sys.path:
        sys.path.insert(0, value)

from reasbook_build_sdk.statement_docs import module_label, source_reading, statement_excerpts  # noqa: E402


SITE_CONFIG: SiteConfig = load_site_config()
GITHUB_OWNER = SITE_CONFIG.github_owner
GITHUB_REPO = SITE_CONFIG.github_repo
GITHUB_BRANCH = SITE_CONFIG.github_branch
SITE_BASE = SITE_CONFIG.site_base
SITE_ROOT = SITE_CONFIG.site_root


# ---------------------------------------------------------------------------
# Configuration and source metadata
# ---------------------------------------------------------------------------


GENERATED_LEAN_HEADER = (
    "/-\n"
    "Authors: Wanli Ma, Zichen Wang\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Generated website code; mathematical source authors are credited separately.\n"
    "-/\n\n"
)


def with_generated_lean_header(content: str, previous: str | None) -> str:
    """Retain attributed file notices when regenerating a Lean page."""
    for index, source in enumerate((content, previous or "")):
        span = header_span(source)
        if span:
            start, end = span
            header = source[start:end]
            if author_field(header, allow_singular=True):
                if index == 0:
                    return content
            else:
                header = header[:-2].rstrip() + "\nAuthors: Wanli Ma, Zichen Wang\n-/"
            if index == 0:
                return source[:start] + header + source[end:]
            prefix = source[:start]
            if content.startswith("\ufeff") and not prefix.startswith("\ufeff"):
                prefix = "\ufeff" + prefix
            return prefix + header + "\n\n" + content.removeprefix("\ufeff")
        text = source.lstrip("\ufeff \t\r\n")
        if text.startswith("/-") and not text.startswith(("/-!", "/--")):
            raise ValueError("refusing to regenerate an unterminated Lean file header")
    bom = "\ufeff" if content.startswith("\ufeff") else ""
    return bom + GENERATED_LEAN_HEADER + content.removeprefix("\ufeff")


def generated_body_first_line(path: Path) -> list[str]:
    """Locate ownership markers after a preserved attribution header."""
    source = path.read_text(encoding="utf-8", errors="replace")
    span = header_span(source)
    if span and author_field(source[span[0]:span[1]], allow_singular=True):
        source = source[span[1]:].lstrip(" \t\r\n")
    else:
        source = source.removeprefix("\ufeff")
    return source.splitlines()[:1]


def write_text_if_changed(path: Path, content: str, *, log: bool = True) -> bool:
    old_content: str | None
    try:
        old_content = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        old_content = None

    if path.suffix == ".lean":
        content = with_generated_lean_header(content, old_content)

    if old_content == content:
        return False

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    temporary = Path(temporary_name)
    try:
        mode = (path.stat().st_mode & 0o777) if path.exists() else 0o644
        os.fchmod(descriptor, mode)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.close(descriptor)
        except OSError:
            pass
        temporary.unlink(missing_ok=True)
        raise
    if log:
        print(f"Wrote {path}")
    return True


BOOK_TITLES = {
    "AlgebraicTopology_May_1999": "A Concise Course in Algebraic Topology (May, 1999)",
    "CombinatorialGroupTheory_Magnus_2004": "Combinatorial Group Theory (Magnus, Karrass and Solitar, 2004)",
    "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017": "Convex Analysis and Monotone Operator Theory in Hilbert Spaces (Bauschke and Combettes, 2017)",
    "FirstOrderMethodsOptimization_Beck_2017": "First-Order Methods in Optimization (Beck, 2017)",
    "IntroductoryLecturesOnConvexOptimization_Nesterov_2004": "Introductory Lectures on Convex Optimization (Nesterov, 2004)",
    "OptimizationTheoryAndMethods_SunYuan_2006": "Optimization Theory and Methods: Nonlinear Programming (Sun and Yuan, 2006)",
    "RiemannSurfaces_Forster_1981": "Lectures on Riemann Surfaces (Forster, 1981)",
    "ConvexAnalysis_Rockafellar_1970": "Convex Analysis (Rockafellar, 1970)",
    "IntegerProgramming_Conforti_2014": "Integer Programming (Conforti et al., 2014)",
    "Analysis2_Tao_2022": "Analysis II (Tao, 2022)",
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": "Introduction to Real Analysis, Volume I (Jiri Lebl, 2025)",
}

PAPER_TITLES = {
    "BFGSMinimumQOrder_Liu_2026": "The Minimum Q-Order of BFGS with Exact Line Search Is One (Liu et al., 2026)",
    "RockafellarSum_2026": "A Counterexample to the Rockafellar Sum Conjecture on c₀ (2026)",
    "DFP_wolfe_local": "Local Convergence of DFP with Wolfe Line Search",
    "glowinski_admm_counterexample": "The Multiplier Step Size of Two-Block ADMM",
    "SmoothMinimization_Nesterov_2004": "Smooth Minimization of Non-Smooth Functions (Nesterov, 2004)",
    "OnSomeLocalRings_Maassaran_2025": "On Some Local Rings (Maassarani, 2025)",
    "TR_LALM_theory": "TR-LALM Theory",
}

BOOK_CHAPTER_TITLES = {
    "Analysis2_Tao_2022": {
        1: "Metric Spaces",
        2: "Continuous Functions on Metric Spaces",
        3: "Uniform Convergence",
        4: "Power Series",
        5: "Fourier Series",
        6: "Several Variable Differential Calculus",
        7: "Lebesgue Measure",
        8: "Lebesgue Integration",
    },
    "ConvexAnalysis_Rockafellar_1970": {
        1: "Part I: Basic Concepts",
        2: "Part II: Topological Properties",
        3: "Part III: Duality Correspondences",
        4: "Part IV: Representation and Inequalities",
    },
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": {
        1: "Real Numbers",
        2: "Sequences and Series",
        3: "Continuous Functions",
        4: "The Derivative",
        5: "The Riemann Integral",
        6: "Sequences of Functions",
        7: "Metric Spaces",
    },
}

BOOK_SECTION_TITLES = {
    "Analysis2_Tao_2022": {
        1: {
            1: "Definitions and Examples",
            2: "Some Point-Set Topology of Metric Spaces",
            3: "Relative Topology",
            4: "Cauchy Sequences and Complete Metric Spaces",
            5: "Compact Metric Spaces",
        },
        2: {
            1: "Continuous Functions",
            2: "Continuity and Product Spaces",
            3: "Continuity and Compactness",
            4: "Continuity and Connectedness",
            5: "Topological Spaces",
        },
        3: {
            1: "Limiting Values of Functions",
            2: "Pointwise and Uniform Convergence",
            3: "Uniform Convergence and Continuity",
            4: "The Metric of Uniform Convergence",
            5: "Series of Functions; the Weierstrass M-Test",
            6: "Uniform Convergence and Integration",
            7: "Uniform Convergence and Derivatives",
            8: "Uniform Approximation by Polynomials",
        },
        4: {
            1: "Formal Power Series",
            2: "Real Analytic Functions",
            3: "Abel's Theorem",
            4: "Multiplication of Power Series",
            5: "The Exponential and Logarithm Functions",
            6: "A Digression on Complex Numbers",
            7: "Trigonometric Functions",
        },
        5: {
            1: "Periodic Functions",
            2: "Inner Products on Periodic Functions",
            3: "Trigonometric Polynomials",
            4: "Periodic Convolutions",
            5: "The Fourier and Plancherel Theorems",
        },
        6: {
            1: "Linear Transformations",
            2: "Derivatives in Several Variable Calculus",
            3: "Partial and Directional Derivatives",
            4: "The Several Variable Calculus Chain Rule",
            5: "Double Derivatives and Clairaut's Theorem",
            6: "The Contraction Mapping Theorem",
            7: "The Inverse Function Theorem in Several Variable Calculus",
            8: "The Implicit Function Theorem",
        },
        7: {
            1: "The Goal: Lebesgue Measure",
            2: "First Attempt: Outer Measure",
            3: "Outer Measure Is not Additive",
            4: "Measurable Sets",
            5: "Measurable Functions",
        },
        8: {
            1: "Simple Functions",
            2: "Integration of Non-negative Measurable Functions",
            3: "Integration of Absolutely Integrable Functions",
            4: "Comparison with the Riemann Integral",
            5: "Fubini's Theorem",
        },
    },
    "ConvexAnalysis_Rockafellar_1970": {
        1: {
            1: "Affine Sets",
            2: "Convex Sets and Cones",
            3: "The Algebra of Convex Sets",
            4: "Convex Functions",
            5: "Functional Operations",
        },
        2: {
            5: "Functional Operations",
            6: "Relative Interiors of Convex Sets",
            7: "Closures of Convex Functions",
            8: "Recession Cones and Unboundedness",
            9: "Some Closedness Criteria",
            10: "Continuity of Convex Functions",
        },
        3: {
            11: "Separation Theorems",
            12: "Conjugates of Convex Functions",
            13: "Support Functions",
            14: "Polars of Convex Sets",
            15: "Polars of Convex Functions",
            16: "Dual Operations",
        },
        4: {
            17: "Caratheodory's Theorem",
            18: "Extreme Points and Faces of Convex Sets",
            19: "Polyhedral Convex Sets and Functions",
            20: "Some Applications of Polyhedral Convexity",
        },
    },
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": {
        1: {
            1: "Basic Properties",
            2: "The Set of Real Numbers",
            3: "Absolute Value and Bounded Functions",
            4: "Intervals and the Size of R",
            5: "Decimal Representation of the Reals",
        },
        2: {
            1: "Sequences and Limits",
            2: "Facts About Limits of Sequences",
            3: "Limit Superior, Limit Inferior, and Bolzano-Weierstrass",
            4: "Cauchy Sequences",
            5: "Series",
            6: "More on Series",
        },
        3: {
            1: "Limits of Functions",
            2: "Continuous Functions",
            3: "Extreme and Intermediate Value Theorems",
            4: "Uniform Continuity",
            5: "Limits at Infinity",
            6: "Monotone Functions and Continuity",
        },
        4: {
            1: "The Derivative",
            2: "Mean Value Theorem",
            3: "Taylor's Theorem",
            4: "Inverse Function Theorem",
        },
        5: {
            1: "The Riemann Integral",
            2: "Properties of the Integral",
            3: "Fundamental Theorem of Calculus",
            4: "The Logarithm and the Exponential",
            5: "Improper Integrals",
        },
        6: {
            1: "Pointwise and Uniform Convergence",
            2: "Interchange of Limits",
            3: "Picard's Theorem",
        },
        7: {
            1: "Metric Spaces",
            2: "Open and Closed Sets",
            3: "Sequences and Convergence",
            4: "Completeness and Compactness",
            5: "Continuous Functions",
            6: "Fixed Point Theorem and Picard's Theorem Again",
        },
    },
}

PAPER_SECTION_TITLES = {
    "SmoothMinimization_Nesterov_2004": {
        1: "Introduction",
        2: "Smooth Approximations of Non-differentiable Functions",
        3: "Fast Gradient Methods",
        4: "Applications",
        5: "Implementation Issues and Modifications",
    },
    "OnSomeLocalRings_Maassaran_2025": {
        1: "Separable Case",
        2: "Lifting the Isomorphisms",
    },
}

TBD_BOOKS = {"IntegerProgramming_Conforti_2014", "ComputationalMethodsInverseProblems_Vogel_2002"}

SKIP_STEMS = {"utils", "tactics", "scratch", "internal", "helper", "helpers"}

OLD_OVERVIEW_BEGIN = "-- BEGIN REASBOOK OVERVIEW (generated by scripts/gen_sections.py)"
OLD_OVERVIEW_END = "-- END REASBOOK OVERVIEW"

CHAPTER_RE = re.compile(r"^(?:chapter_|chap)(\d+)$", re.IGNORECASE)
SECTION_RE = re.compile(r"^section_?(\d+)$", re.IGNORECASE)
PART_RE = re.compile(r"^part_?(\d+)$", re.IGNORECASE)
PAPER_SECTION_RE = re.compile(r"section\d+(?:_part\d+)?", re.IGNORECASE)
ITEM_STEM_RE = re.compile(
    r"^(?P<kind>[A-Za-z][A-Za-z0-9]*)_"
    r"(?P<chapter>\d+)_(?P<tail>[A-Za-z0-9]+(?:_[A-Za-z0-9]+)*)$"
)
PAPER_ITEM_STEM_RE = re.compile(
    r"^(?P<kind>[A-Za-z][A-Za-z0-9]*)_"
    r"(?P<section>[A-Za-z0-9]+)_(?P<tail>[A-Za-z0-9]+(?:_[A-Za-z0-9]+)*)$"
)
ITEM_KINDS = frozenset(
    name.casefold()
    for name in (
        "Alg",
        "Algorithm",
        "Assumption",
        "Construction",
        "Corollary",
        "Corrollary",
        "Crollary",
        "Definition",
        "Equation",
        "Example",
        "Exmaple",
        "Exercise",
        "Fact",
        "Lemma",
        "Method",
        "Notation",
        "Principle",
        "Problem",
        "Program",
        "ProofStep",
        "Proposition",
        "Remark",
        "Text",
        "Theorem",
    )
)
GENERATED_READER_MARKER = (
    "-- This item-style chapter page is generated by scripts/gen_sections.py"
)
GENERATED_PAPER_READER_MARKER = (
    "-- This item-style paper page is generated by scripts/gen_sections.py"
)
GENERATED_PAPER_SECTION_MARKER = (
    "-- This paper section index is generated by scripts/gen_sections.py"
)

_BOOK_METADATA_TITLES: dict[str, str] = {}


# ---------------------------------------------------------------------------
# Entry discovery and naming
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Entry:
    category: str
    module: str
    title: str
    route: str
    book_or_paper: str
    chapter_num: int
    section_num: int
    part_num: int
    stem: str


@dataclass(frozen=True)
class BookItem:
    """A fine-grained declaration module represented by a chapter index link.

    Item-style books can contain hundreds or thousands of modules named like
    ``Definition_1_2_3``.  They are deliberately not :class:`Entry` objects:
    entries become literate targets, while items only contribute lightweight
    links to a generated chapter reader.
    """

    book: str
    module: str
    source_path: str
    chapter_num: int
    section_num: int
    tail_parts: tuple[str, ...]
    kind: str
    stem: str


@dataclass(frozen=True)
class BookSupportModule:
    """A chapter source module that is not a reader item or ordinary section."""

    book: str
    module: str
    source_path: str
    chapter_num: int
    relative_path: str


@dataclass(frozen=True)
class ChapterInventory:
    """Complete classification of the source modules below one chapter dir."""

    book: str
    chapter_num: int
    source_directory: str
    items: tuple[BookItem, ...]
    ordinary_section_modules: tuple[BookSupportModule, ...]
    support_modules: tuple[BookSupportModule, ...]


@dataclass(frozen=True)
class ReaderChapter:
    """A compact generated reader for one chapter of item-style modules."""

    book: str
    chapter_num: int
    route: str
    legacy_routes: tuple[str, ...]
    source_directory: str
    items: tuple[BookItem, ...]
    ordinary_sections: tuple[Entry, ...]
    ordinary_section_modules: tuple[BookSupportModule, ...]
    support_modules: tuple[BookSupportModule, ...]


@dataclass(frozen=True)
class PaperItem:
    """A direct ``Kind_<section>_<tail>`` module indexed by a paper reader."""

    paper: str
    module: str
    source_path: str
    section_token: str
    tail_parts: tuple[str, ...]
    kind: str
    stem: str


@dataclass(frozen=True)
class PaperInventory:
    """Complete classification of the Lean modules below one paper directory."""

    paper: str
    source_directory: str
    items: tuple[PaperItem, ...]
    ordinary_section_modules: tuple[str, ...]
    support_module_count: int


@dataclass(frozen=True)
class PaperReader:
    """A compact, non-root reader for an item-style paper."""

    paper: str
    route: str
    source_directory: str
    items: tuple[PaperItem, ...]
    support_module_count: int


@dataclass(frozen=True)
class PaperSectionIndex:
    """Generated reader for an imports-only paper section with part modules."""

    paper: str
    section_num: int
    route: str
    base: Entry
    parts: tuple[Entry, ...]
    source_path: str


def is_chapter_entry(entry: Entry) -> bool:
    return (
        entry.category == "books"
        and entry.chapter_num > 0
        and entry.section_num == 0
        and entry.part_num == 0
        and CHAPTER_RE.fullmatch(entry.stem) is not None
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "repo_root",
        nargs="?",
        default=None,
        help="Path to the repository root (the directory containing ReasBookWeb/ and ReasBook/).",
    )
    parser.add_argument(
        "--repo-root",
        dest="repo_root_option",
        default=None,
        help="Path to the repository root; equivalent to the positional argument.",
    )
    return parser.parse_args()


def humanize_identifier(s: str) -> str:
    s = s.replace("_", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return s.title() if s else s


def _plain_yaml_scalar(value: str) -> str | None:
    """Parse the small, safe YAML scalar subset needed for ``book.yml``.

    Pulling a YAML runtime into the web generator solely for one display field
    would make isolated release workers less reproducible.  This parser accepts
    a top-level plain, single-quoted, or JSON-compatible double-quoted scalar;
    structured/tagged/multiline values fail closed and fall back to the stable
    identifier-derived title.
    """

    value = value.strip()
    if not value or value in {"|", ">", "~", "null", "Null", "NULL"}:
        return None
    if value[0] in "[{@&*!":
        return None
    if value.startswith('"'):
        try:
            parsed, end = json.JSONDecoder().raw_decode(value)
        except json.JSONDecodeError:
            return None
        remainder = value[end:].strip()
        if remainder and not remainder.startswith("#"):
            return None
        title = parsed if isinstance(parsed, str) else ""
    elif value.startswith("'"):
        chars: list[str] = []
        end = 1
        while end < len(value):
            if value[end] != "'":
                chars.append(value[end])
                end += 1
                continue
            if end + 1 < len(value) and value[end + 1] == "'":
                chars.append("'")
                end += 2
                continue
            end += 1
            break
        else:
            return None
        remainder = value[end:].strip()
        if remainder and not remainder.startswith("#"):
            return None
        title = "".join(chars)
    else:
        # In a plain scalar, a comment starts only at whitespace followed by
        # '#'; hashes embedded in a title remain ordinary text.
        title = re.split(r"\s+#", value, maxsplit=1)[0].strip()

    title = re.sub(r"\s+", " ", title).strip()
    if not title or len(title) > 300 or not title.isprintable():
        return None
    return title


def read_book_metadata_title(book_root: Path) -> str | None:
    """Read a top-level ``title`` scalar without executing YAML features."""

    metadata = next(
        (
            path
            for name in ("book.yml", "book.yaml")
            if (path := book_root / name).is_file()
        ),
        None,
    )
    if metadata is None or metadata.stat().st_size > 1024 * 1024:
        return None
    for raw_line in metadata.read_text(encoding="utf-8", errors="replace").splitlines():
        if raw_line[:1].isspace():
            continue
        match = re.fullmatch(r"title\s*:\s*(.*)", raw_line)
        if match:
            return _plain_yaml_scalar(match.group(1))
    return None


def load_book_metadata_titles(source_root: Path) -> None:
    """Refresh title overrides for the source tree used by this invocation."""

    _BOOK_METADATA_TITLES.clear()
    books_root = source_root / "Books"
    if not books_root.is_dir():
        return
    for book_root in sorted(path for path in books_root.iterdir() if path.is_dir()):
        title = read_book_metadata_title(book_root)
        if title:
            _BOOK_METADATA_TITLES[book_root.name] = title


def module_doc_title(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    m = re.search(r"/(?:-!|--)\s*(.*?)\s*-/", text, re.DOTALL)
    if not m:
        return None
    body = m.group(1)
    lines = []
    for raw in body.splitlines():
        line = raw.strip().lstrip("#").strip()
        if not line:
            continue
        if line.startswith("import "):
            continue
        lines.append(line)
    if not lines:
        return None
    first = lines[0]
    if len(first) > 60:
        return None
    if "`" in first or ":" in first or "." in first:
        return None
    # Chapter headings often include a short book subtitle (for example,
    # "Chapter 01 — Lectures on Riemann Surfaces (Forster, 1981)").
    # Keep the prose guard, but leave room for those descriptive headings.
    if len(first.split()) > 12:
        return None
    if not re.match(r"^(Section|Chapter|Appendix)\b", first, re.IGNORECASE):
        return None
    return first


def chapter_number(parts: Iterable[str]) -> int:
    for p in parts:
        token = p.rsplit(".", 1)[0]
        m = CHAPTER_RE.match(token)
        if m:
            return int(m.group(1))
    return 0


def chapter_title(parts: Iterable[str]) -> str | None:
    for p in parts:
        token = p.rsplit(".", 1)[0]
        m = CHAPTER_RE.match(token)
        if m:
            return f"Chapter {int(m.group(1)):02d}"
    return None


def chapter_title_for_book(book: str, chapter_num: int) -> str:
    named = BOOK_CHAPTER_TITLES.get(book, {}).get(chapter_num)
    if named:
        return f"Chapter {chapter_num:02d} -- {named}"
    return f"Chapter {chapter_num:02d}"


def parse_section_part(stem: str) -> tuple[int, int]:
    section_num = 0
    part_num = 0
    lower = stem.lower()
    numbered_intro = re.match(r"section_(\d+)_(\d+)(?:_|$)", lower)
    if numbered_intro:
        # Item-dominant projects sometimes encode both chapter and section in
        # an ordinary reading-section module (for example Section_8_2_intro).
        section_num = int(numbered_intro.group(2))
    for token in lower.split("_"):
        ms = SECTION_RE.match(token)
        if ms:
            section_num = int(ms.group(1))
            continue
        mp = PART_RE.match(token)
        if mp:
            part_num = int(mp.group(1))
    m2 = re.match(r"section(\d+)", lower)
    if m2:
        section_num = int(m2.group(1))
    m3 = re.search(r"part(\d+)", lower)
    if m3:
        part_num = int(m3.group(1))
    return section_num, part_num


def section_title_from_stem(stem: str) -> str:
    lower = stem.lower()
    if lower in {"book", "paper", "main"}:
        return "Overview"

    sec, part = parse_section_part(stem)
    if sec > 0:
        base = f"Section {sec:02d}"
        if part > 0:
            return f"{base} -- Part {part}"
        return base

    return humanize_identifier(stem)


def entry_label(e: Entry) -> str:
    if e.category == "books":
        section_titles = BOOK_SECTION_TITLES.get(e.book_or_paper, {}).get(
            e.chapter_num, {}
        )
        if e.section_num in section_titles and e.part_num == 0:
            return section_titles[e.section_num]
    if e.category == "papers":
        paper_titles = PAPER_SECTION_TITLES.get(e.book_or_paper, {})
        if e.section_num in paper_titles and e.part_num == 0:
            return paper_titles[e.section_num]
    if e.part_num > 0:
        return ""
    return section_title_from_stem(e.stem)


def readme_label(e: Entry) -> str:
    base = entry_label(e)
    if not base:
        return ""
    if e.category == "books":
        # If title fell back to a generic stem-derived "Section NN", avoid
        # duplicated labels like "0.3 Section 03".
        default_base = section_title_from_stem(e.stem)
        if base == default_base and re.fullmatch(r"Section \d{2}", base):
            return f"Section {e.chapter_num}.{e.section_num}"
        return f"{e.chapter_num}.{e.section_num} {base}"
    if e.category == "papers":
        return f"Section {e.section_num}: {base}"
    return base


def book_title(book: str) -> str:
    if book in _BOOK_METADATA_TITLES:
        return _BOOK_METADATA_TITLES[book]
    if book in BOOK_TITLES:
        return BOOK_TITLES[book]
    return humanize_identifier(book)


def paper_title(paper: str) -> str:
    if paper in PAPER_TITLES:
        return PAPER_TITLES[paper]
    return humanize_identifier(paper)


@lru_cache(maxsize=None)
def _lake_source_layout(source_root: Path) -> tuple[dict[tuple[str, ...], str], tuple[tuple[str, ...], ...]]:
    """Read explicit roots and per-library source directories from Lake."""
    lakefile = source_root / "lakefile.lean"
    if not lakefile.is_file():
        return {}, ()
    lines = lakefile.read_text(encoding="utf-8", errors="replace").splitlines()
    explicit: dict[tuple[str, ...], str] = {}
    directories: set[tuple[str, ...]] = set()
    for index, line in enumerate(lines):
        library = re.match(r"^[ \t]*lean_lib[ \t]+", line.split("--", 1)[0])
        if not library:
            continue
        source_directory: tuple[str, ...] = ()
        roots: list[str] = []
        cursor = index + 1
        while cursor < len(lines):
            candidate = lines[cursor]
            if candidate.strip() and not candidate[0].isspace():
                break
            source_match = re.match(r'^[ \t]*srcDir[ \t]*:=[ \t]*"([^"]+)"', candidate)
            if source_match:
                source_directory = tuple(Path(source_match.group(1)).parts)
                directories.add(source_directory)
            roots_match = re.match(r"^[ \t]*roots[ \t]*:=[ \t*#]*([^]]+)", candidate)
            if roots_match:
                roots.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", roots_match.group(1)))
            cursor += 1
        for root in roots:
            root_path = tuple(Path(*root.split(".")).with_suffix(".lean").parts)
            explicit[source_directory + root_path] = root
    return explicit, tuple(sorted(directories, key=lambda value: (-len(value), value)))


def to_module(source_root: Path, path: Path) -> str:
    rel = path.relative_to(source_root)
    explicit, source_directories = _lake_source_layout(source_root)
    if rel.parts in explicit:
        return explicit[rel.parts]
    for source_directory in source_directories:
        prefix = tuple(rel.parts[:len(source_directory)])
        if prefix == source_directory and len(rel.parts) > len(source_directory):
            return ".".join(rel.with_suffix("").parts[len(source_directory):])
    parts = list(rel.with_suffix("").parts)
    # For aggregate layout (lean_lib Books/Papers), retain the public prefix.
    # For flat layout without explicit per-library srcDir, strip it.
    if len(parts) >= 2 and parts[0] in ("Books", "Papers"):
        if _layout_prefix(source_root, parts[0].lower()) == "":
            parts = parts[1:]
    return ".".join(parts)


@lru_cache(maxsize=None)
def _detect_layout(source_root: Path) -> dict[str, str]:
    """Read lakefile.lean to determine book/paper module prefix.

    Returns a dict with keys 'books' and 'papers', each mapping to the
    module prefix (e.g. 'Books.' or '' for flat layout).
    """
    lakefile = source_root / "lakefile.lean"
    result: dict[str, str] = {"books": "Books.", "papers": "Papers."}
    if not lakefile.is_file():
        return result
    text = lakefile.read_text(encoding="utf-8")
    # Aggregated: lean_lib Books where … lean_lib Papers where
    # Flat:       lean_lib BookName where … srcDir := "Books"
    has_aggregated_books = bool(re.search(r'lean_lib\s+[«"]?Books[»"]?\s', text))
    has_aggregated_papers = bool(re.search(r'lean_lib\s+[«"]?Papers[»"]?\s', text))
    if has_aggregated_books:
        result["books"] = "Books."
    else:
        result["books"] = ""
    if has_aggregated_papers:
        result["papers"] = "Papers."
    else:
        result["papers"] = ""
    return result


def _layout_prefix(source_root: Path, kind: str) -> str:
    """Return the module prefix for books or papers based on lakefile layout."""
    return _detect_layout(source_root)[kind]


def _book_module(source_root: Path, book: str, suffix: str) -> str:
    """Return the full module name for a book's root or chapter."""
    prefix = _layout_prefix(source_root, "books")
    return f"{prefix}{book}.{suffix}"


def _paper_module(source_root: Path, paper: str, leaf: str) -> str:
    """Return the full module name for a paper's root."""
    prefix = _layout_prefix(source_root, "papers")
    return f"{prefix}{paper}.{leaf}"


def normalize_path(path: str) -> str:
    path = path.strip()
    if not path:
        return ""
    has_trailing_slash = path.endswith("/")
    pieces = [piece for piece in path.split("/") if piece]
    if not pieces:
        return ""
    out = "/".join(pieces)
    if has_trailing_slash:
        out += "/"
    return out


def repo_relative_link(path: str) -> str:
    norm = normalize_path(path)
    if not norm:
        return "./"
    return f"./{norm}"


def github_tree_link(path: str) -> str:
    norm = normalize_path(path)
    base = f"https://github.com/{GITHUB_OWNER}/{GITHUB_REPO}/tree/{GITHUB_BRANCH}/"
    return base + norm


def github_blob_link(path: str) -> str:
    norm = normalize_path(path)
    base = f"https://github.com/{GITHUB_OWNER}/{GITHUB_REPO}/blob/{GITHUB_BRANCH}/"
    return base + norm


def route_from_module(module: str) -> str:
    return normalize_path("/".join(part.lower() for part in module.split(".")) + "/")


def local_site_link(route: str) -> str:
    return f"{SITE_ROOT}{normalize_path(route)}"


def route_relative_link(from_route: str, to_route: str) -> str:
    """Link from one site route to another using relative paths."""
    from_norm = normalize_path(from_route)
    to_norm = normalize_path(to_route)
    if not to_norm:
        return ""
    from_base = from_norm[:-1] if from_norm.endswith("/") else from_norm
    if not from_base:
        from_base = "."
    to_has_trailing = to_norm.endswith("/")
    to_target = to_norm[:-1] if to_has_trailing else to_norm
    rel = posixpath.relpath(to_target, start=from_base)
    if rel == ".":
        return "./"
    return f"{rel}/" if to_has_trailing else rel


def docs_relative_site_link(module: str, route: str) -> str:
    """Link from docs/<module>.html to a site route without hardcoding repo prefix."""
    route_norm = normalize_path(route)
    if not route_norm:
        return ""
    depth = max(1, len([part for part in module.split(".") if part]))
    return f"{'../' * depth}{route_norm}"


def _module_to_docs_path(source_root: Path, module_name: str) -> str:
    """Convert a Lean module name to a docs/ReasBook/ URL path.

    doc-gen4 follows the logical module name, not the library's ``srcDir``.
    ``source_root`` remains in the signature for callers that already carry
    the project layout alongside the module.
    """
    _ = source_root
    return "/".join(module_name.split("."))


def project_docs_path(source_root: Path, project: str, kind: str) -> str:
    """Link the same root module that the documentation builder receives."""

    from reasbook_build_sdk.targets import library_target

    # Explicit Lake roots need not include a compatibility aggregate module.
    # In particular BFGS has both a real project-named aggregate and Paper;
    # only the former is selected by the release documentation build.
    target = library_target(source_root, project, kind)
    return _module_to_docs_path(source_root, target)


def docs_relative_doc_link(source_root: Path, from_module: str, to_module: str) -> str:
    _ = from_module
    to_path = _module_to_docs_path(source_root, to_module)
    return portable_site_link(f"docs/ReasBook/{to_path}.html")


def portable_site_link(route: str) -> str:
    norm = normalize_path(route)
    return f"{SITE_ROOT}{norm}" if norm else SITE_ROOT


def published_site_link(route: str) -> str:
    norm = normalize_path(route)
    return f"{SITE_BASE}{norm}" if norm else SITE_BASE


# ---------------------------------------------------------------------------
# Source entry collection
# ---------------------------------------------------------------------------


def should_include_book(
    path: Path, reader_source_directories: frozenset[Path] = frozenset()
) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False

    if stem == "book":
        return True

    # Fine-grained item modules are represented by a generated chapter index,
    # not one expensive literate target per declaration.  Only a fully valid
    # direct-child match is suppressed; malformed/misplaced modules continue
    # through the ordinary discovery path instead of disappearing from both.
    if parse_item_identity(path) is not None:
        return path.parent not in reader_source_directories

    # A chapter aggregation module is site structure.  Its inclusion must not
    # depend on whether the prose title happens to pass ``module_doc_title``'s
    # conservative heading heuristic.
    if CHAPTER_RE.fullmatch(path.stem):
        return True

    parts_lower = [p.lower() for p in path.parts]
    in_chapter_tree = any(CHAPTER_RE.match(p) for p in parts_lower) or (
        CHAPTER_RE.match(stem) is not None
    )
    if not in_chapter_tree:
        return False

    if stem.startswith("section"):
        # Nested item implementation files (e.g. Lemma_13_6_3/section13325)
        # are supporting modules, not book sections. Do not invent numbering.
        return CHAPTER_RE.fullmatch(path.parent.name) is not None

    return module_doc_title(path) is not None


def should_include_paper(
    path: Path, reader_source_directories: frozenset[Path] = frozenset(),
    *, paper_root: Path,
) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False
    if stem in {"paper", "main"}:
        return True
    if parse_paper_item_identity(path) is not None:
        return path.parent not in reader_source_directories
    # Automatic sections are direct, numbered paper children. Internal support
    # modules such as ReasLib/.../SectionContraction and nested section13325
    # must not become reading entries or links outside the published docs.
    # Explicit reading manifests and imported facades are handled separately.
    return path.parent == paper_root and PAPER_SECTION_RE.fullmatch(stem) is not None


def parse_item_identity(path: Path) -> tuple[str, int, tuple[str, ...]] | None:
    """Parse a trusted direct ``ChapNN/Kind_<chapter>_<tail>`` item name."""

    directory_match = CHAPTER_RE.fullmatch(path.parent.name)
    match = ITEM_STEM_RE.fullmatch(path.stem)
    if directory_match is None or match is None:
        return None
    kind = match.group("kind")
    if kind.casefold() not in ITEM_KINDS:
        return None
    directory_chapter = int(directory_match.group(1))
    stem_chapter = int(match.group("chapter"))
    if directory_chapter != stem_chapter:
        return None
    tail = tuple(match.group("tail").split("_"))
    return kind, stem_chapter, tail


def parse_paper_item_identity(
    path: Path,
) -> tuple[str, str, tuple[str, ...]] | None:
    """Parse a trusted direct paper ``Kind_<section>_<tail>`` item name."""

    if path.parent.parent.name != "Papers":
        return None
    match = PAPER_ITEM_STEM_RE.fullmatch(path.stem)
    if match is None:
        return None
    kind = match.group("kind")
    if kind.casefold() not in ITEM_KINDS:
        return None
    return kind, match.group("section"), tuple(match.group("tail").split("_"))


def parse_book_item(path: Path, source_root: Path) -> BookItem | None:
    """Return metadata for a trusted item root in a chapter directory."""

    books_root = source_root / "Books"
    try:
        rel = path.relative_to(books_root)
    except ValueError:
        return None
    if len(rel.parts) < 3:
        return None

    identity = parse_item_identity(path)
    if identity is None:
        return None
    kind, stem_chapter, tail = identity

    book = rel.parts[0]
    if not project_enabled("books", book) or book in TBD_BOOKS:
        return None
    module = to_module(source_root, path)
    if module in SKIP_MODULES:
        return None
    section_num = int(tail[0]) if len(tail) >= 2 and tail[0].isdigit() else 0
    return BookItem(
        book=book,
        module=module,
        source_path=(Path("ReasBook") / "Books" / rel).as_posix(),
        chapter_num=stem_chapter,
        section_num=section_num,
        tail_parts=tail,
        kind=kind,
        stem=path.stem,
    )


def _natural_parts(parts: tuple[str, ...]) -> tuple[tuple[int, int | str], ...]:
    return tuple(
        (0, int(part)) if part.isdigit() else (1, part.casefold()) for part in parts
    )


def book_item_sort_key(item: BookItem) -> tuple[object, ...]:
    return (
        item.book.casefold(),
        item.chapter_num,
        item.section_num,
        _natural_parts(item.tail_parts),
        item.kind.casefold(),
        item.stem.casefold(),
    )


def source_module_metadata(
    path: Path, source_root: Path, book: str, chapter_num: int, chapter_dir: Path
) -> BookSupportModule:
    rel = path.relative_to(source_root / "Books")
    return BookSupportModule(
        book=book,
        module=to_module(source_root, path),
        source_path=(Path("ReasBook") / "Books" / rel).as_posix(),
        chapter_num=chapter_num,
        relative_path=path.relative_to(chapter_dir).as_posix(),
    )


def collect_chapter_inventories(source_root: Path) -> list[ChapterInventory]:
    """Classify every Lean source below each selected chapter directory."""

    books_root = source_root / "Books"
    if not books_root.is_dir():
        return []

    inventories: list[ChapterInventory] = []
    seen_chapters: set[tuple[str, int]] = set()
    for chapter_dir in sorted(
        path
        for path in books_root.rglob("*")
        if path.is_dir() and CHAPTER_RE.fullmatch(path.name)
    ):
        rel_dir = chapter_dir.relative_to(books_root)
        if len(rel_dir.parts) < 2:
            continue
        book = rel_dir.parts[0]
        if not project_enabled("books", book) or book in TBD_BOOKS:
            continue
        chapter_num = int(CHAPTER_RE.fullmatch(chapter_dir.name).group(1))
        chapter_key = (book, chapter_num)
        if chapter_key in seen_chapters:
            raise ValueError(
                "multiple source directories represent reader chapter "
                f"{book}/{chapter_num:02d}"
            )
        seen_chapters.add(chapter_key)

        items: list[BookItem] = []
        ordinary: list[BookSupportModule] = []
        support: list[BookSupportModule] = []
        for path in sorted(chapter_dir.rglob("*.lean")):
            if path.parent == chapter_dir and path.stem.casefold().startswith(
                "section"
            ):
                ordinary.append(
                    source_module_metadata(
                        path, source_root, book, chapter_num, chapter_dir
                    )
                )
                continue
            item = parse_book_item(path, source_root)
            if item is not None:
                items.append(item)
                continue
            support.append(
                source_module_metadata(
                    path, source_root, book, chapter_num, chapter_dir
                )
            )

        items.sort(key=book_item_sort_key)
        inventories.append(
            ChapterInventory(
                book=book,
                chapter_num=chapter_num,
                source_directory=(Path("ReasBook") / "Books" / rel_dir).as_posix(),
                items=tuple(items),
                ordinary_section_modules=tuple(ordinary),
                support_modules=tuple(support),
            )
        )

    modules = [item.module for inventory in inventories for item in inventory.items]
    if len(modules) != len(set(modules)):
        raise ValueError("item-style discovery returned duplicate Lean modules")
    return inventories


def parse_paper_item(path: Path, source_root: Path) -> PaperItem | None:
    """Return metadata for a trusted item at the root of a paper directory."""

    papers_root = source_root / "Papers"
    try:
        rel = path.relative_to(papers_root)
    except ValueError:
        return None
    if len(rel.parts) != 2:
        return None
    identity = parse_paper_item_identity(path)
    if identity is None:
        return None
    kind, section_token, tail = identity
    paper = rel.parts[0]
    if not project_enabled("papers", paper):
        return None
    module = to_module(source_root, path)
    if module in SKIP_MODULES:
        return None
    return PaperItem(
        paper=paper,
        module=module,
        source_path=(Path("ReasBook") / "Papers" / rel).as_posix(),
        section_token=section_token,
        tail_parts=tail,
        kind=kind,
        stem=path.stem,
    )


def paper_item_sort_key(item: PaperItem) -> tuple[object, ...]:
    section_key: tuple[int, int | str] = (
        (0, int(item.section_token))
        if item.section_token.isdigit()
        else (1, item.section_token.casefold())
    )
    return (
        item.paper.casefold(),
        section_key,
        _natural_parts(item.tail_parts),
        item.kind.casefold(),
        item.stem.casefold(),
    )


def collect_paper_inventories(source_root: Path) -> list[PaperInventory]:
    """Classify every Lean source below each selected paper directory."""

    papers_root = source_root / "Papers"
    if not papers_root.is_dir():
        return []

    inventories: list[PaperInventory] = []
    for paper_dir in sorted(path for path in papers_root.iterdir() if path.is_dir()):
        paper = paper_dir.name
        if not project_enabled("papers", paper):
            continue
        items: list[PaperItem] = []
        ordinary: list[str] = []
        support_count = 0
        for path in sorted(paper_dir.rglob("*.lean")):
            item = parse_paper_item(path, source_root)
            if item is not None:
                items.append(item)
            elif path.parent == paper_dir and PAPER_SECTION_RE.fullmatch(path.stem):
                ordinary.append(to_module(source_root, path))
            else:
                support_count += 1
        items.sort(key=paper_item_sort_key)
        inventories.append(
            PaperInventory(
                paper=paper,
                source_directory=(Path("ReasBook") / "Papers" / paper).as_posix(),
                items=tuple(items),
                ordinary_section_modules=tuple(sorted(ordinary)),
                support_module_count=support_count,
            )
        )
    modules = [item.module for inventory in inventories for item in inventory.items]
    if len(modules) != len(set(modules)):
        raise ValueError("item-style paper discovery returned duplicate Lean modules")
    return inventories


def paper_inventory_uses_item_reader(inventory: PaperInventory) -> bool:
    """Whether a complete paper inventory is unambiguously item-dominant."""

    item_count = len(inventory.items)
    ordinary_count = len(inventory.ordinary_section_modules)
    return item_count > 0 and (
        ordinary_count == 0 or (item_count >= 5 and item_count >= 4 * ordinary_count)
    )


def collect_paper_readers(
    inventories: Iterable[PaperInventory],
) -> list[PaperReader]:
    return sorted(
        (
            PaperReader(
                paper=inventory.paper,
                route=f"papers/{inventory.paper.lower()}/items/",
                source_directory=inventory.source_directory,
                items=inventory.items,
                support_module_count=inventory.support_module_count,
            )
            for inventory in inventories
            if paper_inventory_uses_item_reader(inventory)
        ),
        key=lambda reader: reader.paper.casefold(),
    )


def inventory_uses_item_reader(inventory: ChapterInventory) -> bool:
    """Whether a complete chapter inventory is unambiguously item-dominant."""

    item_count = len(inventory.items)
    ordinary_count = len(inventory.ordinary_section_modules)
    return item_count > 0 and (
        ordinary_count == 0 or (item_count >= 5 and item_count >= 4 * ordinary_count)
    )


def collect_reader_chapters(
    entries: list[Entry], inventories: Iterable[ChapterInventory]
) -> list[ReaderChapter]:
    """Derive readers only from complete, item-dominant inventories."""

    legacy_by_key: dict[tuple[str, int], set[str]] = {}
    for entry in entries:
        if is_chapter_entry(entry):
            legacy_by_key.setdefault(
                (entry.book_or_paper, entry.chapter_num), set()
            ).add(entry.route)

    entries_by_module = {entry.module: entry for entry in entries}
    chapters: list[ReaderChapter] = []
    for inventory in inventories:
        item_reader = inventory_uses_item_reader(inventory)
        if not item_reader and not inventory.ordinary_section_modules:
            continue
        book = inventory.book
        chapter_num = inventory.chapter_num
        route = f"books/{book.lower()}/chapters/chap{chapter_num:02d}/"
        legacy_routes = tuple(
            sorted(legacy_by_key.get((book, chapter_num), set()) - {route})
        )
        chapters.append(
            ReaderChapter(
                book=book,
                chapter_num=chapter_num,
                route=route,
                legacy_routes=legacy_routes,
                source_directory=inventory.source_directory,
                items=inventory.items if item_reader else (),
                ordinary_sections=tuple(
                    entry
                    for source in inventory.ordinary_section_modules
                    if (entry := entries_by_module.get(source.module)) is not None
                ),
                ordinary_section_modules=inventory.ordinary_section_modules,
                support_modules=inventory.support_modules,
            )
        )
    return sorted(
        chapters, key=lambda value: (value.book.casefold(), value.chapter_num)
    )


def collect_entries(
    source_root: Path,
    inventories: Iterable[ChapterInventory] = (),
    paper_inventories: Iterable[PaperInventory] = (),
) -> list[Entry]:
    entries: list[Entry] = []

    books_root = source_root / "Books"
    papers_root = source_root / "Papers"
    reader_source_directories = frozenset(
        source_root.parent / inventory.source_directory
        for inventory in inventories
        if inventory_uses_item_reader(inventory)
    )
    paper_reader_source_directories = frozenset(
        source_root.parent / inventory.source_directory
        for inventory in paper_inventories
        if paper_inventory_uses_item_reader(inventory)
    )
    configured_papers: set[str] = set()
    facade_sources: set[Path] = set()
    for paper_dir in sorted(papers_root.iterdir()) if papers_root.is_dir() else ():
        if not paper_dir.is_dir() or not project_enabled("papers", paper_dir.name):
            continue
        for facade in paper_dir.glob("*.lean"):
            directory = paper_dir / facade.stem
            if not directory.is_dir():
                continue
            imports = set(re.findall(r"^(?:public\s+)?import\s+([A-Za-z0-9_'.]+)",
                facade.read_text(encoding="utf-8"), re.MULTILINE))
            for path in directory.glob("*.lean"):
                if to_module(source_root, path) in imports:
                    facade_sources.add(path)
        manifest = paper_dir / "tools" / "verso_modules.json"
        if not paper_dir.is_dir() or not project_enabled("papers", paper_dir.name) or not manifest.is_file():
            continue
        plan = json.loads(manifest.read_text(encoding="utf-8"))
        sources = {to_module(source_root, path): path for path in paper_dir.rglob("*.lean")}
        for number, row in enumerate(plan["modules"], start=1):
            module, slug = row["module"], row["slug"]
            if module not in sources or re.fullmatch(r"[a-z0-9][a-z0-9-]*", slug) is None:
                raise ValueError(f"invalid Verso reading module for {paper_dir.name}: {row}")
            entries.append(Entry("papers", module, row["title"],
                f"papers/{paper_dir.name.lower()}/sections/{slug}/", paper_dir.name,
                0, number, 0, slug))
        configured_papers.add(paper_dir.name)

    for path in sorted(books_root.rglob("*.lean")):
        if not should_include_book(path, reader_source_directories):
            continue
        module = to_module(source_root, path)
        if module in SKIP_MODULES:
            continue
        rel = path.relative_to(books_root)
        book = rel.parts[0]
        if not project_enabled("books", book):
            continue
        if book in TBD_BOOKS:
            continue
        ch_title = chapter_title(rel.parts)
        structural_chapter = CHAPTER_RE.fullmatch(path.stem) is not None
        sec_title = module_doc_title(path) or (
            chapter_title_for_book(book, chapter_number(rel.parts))
            if structural_chapter
            else section_title_from_stem(path.stem)
        )
        title_parts = [book_title(book)]
        if ch_title:
            title_parts.append(ch_title)
        if not (ch_title and sec_title.strip().lower() == ch_title.strip().lower()):
            title_parts.append(sec_title)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="books",
                module=module,
                title=" -- ".join(title_parts),
                route=route_from_module(module),
                book_or_paper=book,
                chapter_num=chapter_number(rel.parts),
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
            )
        )

    for path in sorted(papers_root.rglob("*.lean")):
        rel = path.relative_to(papers_root)
        paper = rel.parts[0]
        if not should_include_paper(
            path, paper_reader_source_directories, paper_root=papers_root / paper
        ) and path not in facade_sources:
            continue
        module = to_module(source_root, path)
        if module in SKIP_MODULES:
            continue
        if not project_enabled("papers", paper):
            continue
        if paper in configured_papers and path != papers_root / paper / "Paper.lean":
            continue
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="papers",
                module=module,
                title=f"{paper_title(paper)} -- {sec_title}",
                route=route_from_module(module),
                book_or_paper=paper,
                chapter_num=0,
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
            )
        )

    entries.sort(
        key=lambda e: (
            0 if e.category == "books" else 1,
            e.book_or_paper.lower(),
            e.chapter_num,
            e.section_num,
            e.part_num,
            e.stem,
        )
    )
    return entries


def _lean_code_without_comments(text: str) -> str:
    """Remove Lean comments while preserving code and string literals.

    The scanner understands nested block comments.  It is intentionally used
    only for the conservative imports-only check below; any unfamiliar code
    left behind makes that check fail closed.
    """

    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if char == "\n":
                    out.append("\n")
                index += 1
            continue
        if in_string:
            out.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "--":
            newline = text.find("\n", index + 2)
            if newline < 0:
                break
            out.append("\n")
            index = newline + 1
            continue
        if pair == "/-":
            block_depth = 1
            index += 2
            continue
        out.append(char)
        if char == '"':
            in_string = True
        index += 1
    return "".join(out)


def lean_imports_if_imports_only(path: Path) -> frozenset[str] | None:
    """Return exact imports when a nonempty module has no other commands."""

    code = _lean_code_without_comments(
        path.read_text(encoding="utf-8", errors="replace")
    )
    lines = [line.strip() for line in code.splitlines() if line.strip()]
    if not lines:
        return None
    imports: set[str] = set()
    for line in lines:
        match = re.fullmatch(r"import\s+([A-Za-z0-9_'.]+)", line)
        if match is None:
            return None
        imports.add(match.group(1))
    return frozenset(imports)


def paper_entry_source_file(source_root: Path, entry: Entry) -> Path | None:
    paper_dir = source_root / "Papers" / entry.book_or_paper
    candidates = [
        path
        for path in paper_dir.glob("*.lean")
        if path.stem.casefold() == entry.stem.casefold()
    ]
    if len(candidates) > 1:
        raise ValueError(
            "ambiguous paper source files for "
            f"{entry.book_or_paper}/{entry.stem}: "
            + ", ".join(str(path) for path in candidates)
        )
    return candidates[0] if candidates else None


def collect_paper_section_indexes(
    source_root: Path, entries: Iterable[Entry]
) -> list[PaperSectionIndex]:
    """Find imports-only paper section aggregators that own child parts."""

    bases: dict[tuple[str, int], Entry] = {}
    parts: dict[tuple[str, int], list[Entry]] = {}
    for entry in entries:
        if entry.category != "papers" or entry.section_num <= 0:
            continue
        key = (entry.book_or_paper, entry.section_num)
        if entry.part_num == 0:
            if key in bases:
                raise ValueError(f"duplicate paper section base for {key!r}")
            bases[key] = entry
        else:
            parts.setdefault(key, []).append(entry)

    indexes: list[PaperSectionIndex] = []
    for key, part_entries in sorted(parts.items()):
        base = bases.get(key)
        if base is None:
            continue
        source_file = paper_entry_source_file(source_root, base)
        if source_file is None:
            continue
        imported_modules = lean_imports_if_imports_only(source_file)
        required_part_modules = {entry.module for entry in part_entries}
        if imported_modules is None or not required_part_modules.issubset(
            imported_modules
        ):
            continue
        rel = source_file.relative_to(source_root.parent).as_posix()
        indexes.append(
            PaperSectionIndex(
                paper=base.book_or_paper,
                section_num=base.section_num,
                route=base.route,
                base=base,
                parts=tuple(
                    sorted(part_entries, key=lambda entry: (entry.part_num, entry.stem))
                ),
                source_path=rel,
            )
        )
    return indexes


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


# ---------------------------------------------------------------------------
# Lean and Web artifact rendering
# ---------------------------------------------------------------------------


def emit_literate_manifest(entries: list[Entry]) -> str:
    """Return the deterministic machine-readable input for literate caching."""

    modules = [entry.module for entry in entries]
    if len(modules) != len(set(modules)):
        raise ValueError("site entry discovery returned duplicate Lean modules")
    return (
        json.dumps(
            {"schema_version": 1, "modules": modules},
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    )


def emit_sections(
    entries: list[Entry], reader_chapters: Iterable[ReaderChapter] = (),
    *, source_root: Path,
) -> str:
    reader_chapters = tuple(reader_chapters)
    books: dict[str, dict] = {}
    papers: dict[str, dict] = {}

    def ensure_book(book: str) -> dict:
        if book not in books:
            books[book] = {
                "slug": book.lower(),
                "title": book_title(book),
                "home": "",
                "chapters": {},
            }
        return books[book]

    def ensure_chapter(work: dict, book: str, chapter_num: int) -> dict:
        chapters: dict[int, dict] = work["chapters"]
        if chapter_num not in chapters:
            chapters[chapter_num] = {
                "number": chapter_num,
                "title": f"Chapter {chapter_num:02d}",
                "route": f"books/{book.lower()}/chapters/chap{chapter_num:02d}/",
                "sections": {},
            }
        return chapters[chapter_num]

    def ensure_paper(paper: str) -> dict:
        if paper not in papers:
            papers[paper] = {
                "slug": paper.lower(),
                "title": paper_title(paper),
                "home": "",
                "sections": {},
            }
        return papers[paper]

    for e in entries:
        if e.category == "books":
            work = ensure_book(e.book_or_paper)
            if e.stem == "book":
                work["home"] = f"books/{e.book_or_paper.lower()}/"
                continue

            if e.chapter_num <= 0:
                continue

            chapter = ensure_chapter(work, e.book_or_paper, e.chapter_num)

            if e.section_num <= 0 and e.part_num == 0:
                chapter["route"] = e.route
                continue
            if e.section_num <= 0:
                continue

            sections: dict[int, dict] = chapter["sections"]
            if e.section_num not in sections:
                sections[e.section_num] = {
                    "number": e.section_num,
                    "title": entry_label(e) or f"Section {e.section_num:02d}",
                    "route": "",
                    "parts": [],
                }
            section = sections[e.section_num]
            if e.part_num == 0:
                section["title"] = entry_label(e) or section["title"]
                section["route"] = e.route
            else:
                section["parts"].append(
                    {
                        "number": e.part_num,
                        "title": f"Part {e.part_num}",
                        "route": e.route,
                    }
                )
            continue

        if e.category != "papers":
            continue

        work = ensure_paper(e.book_or_paper)
        if e.stem in {"paper", "main"}:
            work["home"] = f"papers/{e.book_or_paper.lower()}/"
            continue
        if e.section_num <= 0:
            continue

        sections: dict[int, dict] = work["sections"]
        if e.section_num not in sections:
            sections[e.section_num] = {
                "number": e.section_num,
                "title": entry_label(e)
                or section_title_from_stem(f"section{e.section_num:02d}"),
                "route": "",
                "parts": [],
            }
        section = sections[e.section_num]
        if e.part_num == 0:
            section["title"] = entry_label(e) or section["title"]
            section["route"] = e.route
        else:
            section["parts"].append(
                {"number": e.part_num, "title": f"Part {e.part_num}", "route": e.route}
            )

    # Item-style readers are derived from source directories rather than from
    # individual literate entries.  Materialize their chapter nodes after the
    # entry pass so the canonical reader route wins over a flat-layout legacy
    # aggregation-module route.
    for reader in reader_chapters:
        work = ensure_book(reader.book)
        chapter = ensure_chapter(work, reader.book, reader.chapter_num)
        chapter["route"] = reader.route
        # Link each reading file directly to its content in the chapter, not
        # to the former intermediate section/aggregation pages. A multi-clause
        # statement still has one navigation entry for its owning item file.
        chapter["sections"] = {}
        chapter["items"] = [
            {"title": label, "module": module,
             "anchor": module.casefold().replace(".", "-") if has_statement else "",
             "source": source_path}
            for module, label, source_path, has_statement in chapter_reading_modules(source_root, reader)
        ]
        chapter["items"].extend(
            {"title": book_item_label(item), "module": item.module,
             "anchor": "" if "no statement yet" in item_reading_links(source_root, item) else item_anchor(item),
             "source": item.source_path}
            for item in sorted(reader.items, key=book_item_sort_key)
        )

    books_payload: list[dict] = []
    for book in sorted(books):
        work = books[book]
        chapters_payload: list[dict] = []
        chapters: dict[int, dict] = work["chapters"]
        for chapter_num in sorted(chapters):
            chapter = chapters[chapter_num]
            chapter_sections: dict[int, dict] = chapter["sections"]
            sections_payload: list[dict] = []
            for section_num in sorted(chapter_sections):
                section = chapter_sections[section_num]
                parts_payload = sorted(
                    section["parts"],
                    key=lambda p: (p["number"], p["route"]),
                )
                section_title = section["title"] or f"Section {section_num:02d}"
                section_route = section["route"]
                sections_payload.append(
                    {
                        "number": section_num,
                        "title": section_title,
                        "route": section_route,
                        "parts": parts_payload,
                    }
                )
            chapters_payload.append(
                {
                    "number": chapter_num,
                    "title": chapter["title"],
                    "route": chapter["route"],
                    "sections": sections_payload,
                    "items": chapter.get("items", []),
                }
            )
        books_payload.append(
            {
                "slug": work["slug"],
                "title": work["title"],
                "home": work["home"],
                "chapters": chapters_payload,
            }
        )

    papers_payload: list[dict] = []
    for paper in sorted(papers):
        work = papers[paper]
        section_map: dict[int, dict] = work["sections"]
        sections_payload: list[dict] = []
        for section_num in sorted(section_map):
            section = section_map[section_num]
            parts_payload = sorted(
                section["parts"],
                key=lambda p: (p["number"], p["route"]),
            )
            sections_payload.append(
                {
                    "number": section_num,
                    "title": section["title"],
                    "route": section["route"],
                    "parts": parts_payload,
                }
            )
        papers_payload.append(
            {
                "slug": work["slug"],
                "title": work["title"],
                "home": work["home"],
                "sections": sections_payload,
            }
        )

    payload = {"books": books_payload, "papers": papers_payload}
    sidebar_json = json.dumps(payload, ensure_ascii=True, separators=(",", ":"))

    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("namespace ReasBookSite.Sections")
    lines.append("")
    lines.append("def sections : Array (Lean.Name × String) := #[")
    for e in entries:
        lines.append(f"  (`{e.module}, {lean_string(e.title)}),")
    lines.append("]")
    lines.append("")
    lines.append("def routes : Array (String × Lean.Name) := #[")
    for e in entries:
        lines.append(f"  ({lean_string(e.route)}, `{e.module}),")
    lines.append("]")
    lines.append("")
    lines.append(f"def siteRoot : String := {lean_string(SITE_ROOT)}")
    lines.append(f"def siteBase : String := {lean_string(SITE_ROOT)}")
    lines.append(
        f"def docsRoot : String := {lean_string(local_site_link('docs/ReasBook/'))}"
    )
    lines.append(
        f"def staticRoot : String := {lean_string(local_site_link('static/style.css'))}"
    )
    lines.append("")
    lines.append(f"def sidebarDataJson : String := {lean_string(sidebar_json)}")
    lines.append("")
    lines.append("end ReasBookSite.Sections")
    lines.append("")
    return "\n".join(lines)


def reader_chapter_module(reader: ReaderChapter) -> str:
    return (
        f"ReasBookSite.WorkPages.Books.{lean_module_name(reader.book)}."
        f"Chap{reader.chapter_num:02d}"
    )


def paper_reader_module(reader: PaperReader) -> str:
    return f"ReasBookSite.WorkPages.Papers.{lean_module_name(reader.paper)}.Items"


def paper_section_index_module(index: PaperSectionIndex) -> str:
    return (
        f"ReasBookSite.WorkPages.Papers.{lean_module_name(index.paper)}."
        f"Section{index.section_num:02d}"
    )


def emit_route_table(
    entries: list[Entry],
    reader_chapters: Iterable[ReaderChapter] = (),
    paper_readers: Iterable[PaperReader] = (),
    paper_section_indexes: Iterable[PaperSectionIndex] = (),
) -> str:
    intro_book_slug = "introductiontorealanalysisvolumei_jirilebl_2025"
    readers = list(reader_chapters)
    item_paper_readers = list(paper_readers)
    section_indexes = list(paper_section_indexes)
    reader_keys = {(reader.book, reader.chapter_num) for reader in readers}
    section_index_by_module = {index.base.module: index for index in section_indexes}

    def alias_routes(e: Entry) -> list[str]:
        if e.category != "books":
            return []
        prefix = f"books/{intro_book_slug}/"
        if e.route.startswith(prefix + "chapters/chap00/"):
            return [e.route[len(prefix) :]]
        return []

    def work_page_module(e: Entry) -> str:
        if e.category == "books":
            return f"ReasBookSite.WorkPages.Books.{e.book_or_paper}"
        return f"ReasBookSite.WorkPages.Papers.{e.book_or_paper}"

    def is_primary_paper_root(e: Entry) -> bool:
        """Only the project-owned Paper.lean gets the canonical paper route.

        A paper may also contain nested compatibility modules such as
        `DFPWolfe/Paper.lean`; those modules remain literate inputs but must not
        claim the project's landing route a second time.
        """
        parts = e.module.split(".")
        return (
            e.category == "papers"
            and e.stem in {"paper", "main"}
            and (len(parts) == 1 or parts[-2].casefold() == e.book_or_paper.casefold()
                 or parts[-1].casefold() == e.book_or_paper.casefold())
        )

    work_page_imports = {
        work_page_module(e)
        for e in entries
        if (e.category == "books" and e.stem == "book") or is_primary_paper_root(e)
    }
    work_page_imports.update(reader_chapter_module(reader) for reader in readers)
    work_page_imports.update(
        paper_reader_module(reader) for reader in item_paper_readers
    )
    work_page_imports.update(
        paper_section_index_module(index) for index in section_indexes
    )

    bindings: list[tuple[str, str]] = []
    for entry in entries:
        if (
            is_chapter_entry(entry)
            and (entry.book_or_paper, entry.chapter_num) in reader_keys
        ):
            # The generated reader owns both canonical and legacy chapter
            # routes; the aggregation module remains a compact literate cache
            # input but is not exposed as a second page at the same route.
            continue
        if entry.category == "books" and entry.stem == "book":
            target = work_page_module(entry)
            bindings.append((f"books/{entry.book_or_paper.lower()}/", target))
            bindings.append((entry.route, target))
            continue
        if is_primary_paper_root(entry):
            target = work_page_module(entry)
            bindings.append((f"papers/{entry.book_or_paper.lower()}/", target))
            bindings.append((entry.route, f"Book.{entry.module}"))
            continue
        if entry.module in section_index_by_module:
            # Imports-only section aggregators retain their literate/API input,
            # but their user-facing route is a generated index of all parts.
            continue
        target = f"Book.{entry.module}"
        bindings.append((entry.route, target))
        bindings.extend((alias, target) for alias in alias_routes(entry))

    for reader in readers:
        target = reader_chapter_module(reader)
        bindings.append((reader.route, target))
        bindings.extend((route, target) for route in reader.legacy_routes)
    for reader in item_paper_readers:
        bindings.append((reader.route, paper_reader_module(reader)))
    for index in section_indexes:
        bindings.append((index.route, paper_section_index_module(index)))

    owner_by_route: dict[str, str] = {}
    for route, target in bindings:
        previous = owner_by_route.get(route)
        if previous is not None:
            detail = (
                f"{previous} != {target}"
                if previous != target
                else f"duplicate {target}"
            )
            raise ValueError(f"generated route collision for {route!r}: {detail}")
        owner_by_route[route] = target

    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("import VersoBlog")
    lines.append("import ReasBookSite.Home")
    lines.append("import Book")
    for mod in sorted(work_page_imports):
        lines.append(f"import {mod}")
    lines.append("")
    lines.append("open Verso Genre Blog Site Syntax")
    lines.append("")
    lines.append("set_option maxHeartbeats 100000000")
    lines.append("set_option maxRecDepth 200000")
    lines.append("")
    lines.append("namespace ReasBookSite.RouteTable")
    lines.append("")
    lines.append('scoped syntax "reasbook_site_dir" : dir_spec')
    lines.append("")
    lines.append("macro_rules")
    lines.append("  | `(dir_spec| reasbook_site_dir) =>")
    lines.append("    `(dir_spec| /")
    lines.append('      static "static" ← "./static_files"')
    for route, target in bindings:
        lines.append(f"      {lean_string(route)} {target}")
    lines.append("    )")
    lines.append("")
    lines.append("def reasbook_site : Site := site ReasBookSite.Home /")
    lines.append('  static "static" ← "./static_files"')
    for route, target in bindings:
        lines.append(f"  {lean_string(route)} {target}")
    lines.append("")
    lines.append("end ReasBookSite.RouteTable")
    lines.append("")
    return "\n".join(lines)


def fragment_owned_routes(
    entries: list[Entry],
    reader_chapters: Iterable[ReaderChapter] = (),
    paper_readers: Iterable[PaperReader] = (),
    paper_section_indexes: Iterable[PaperSectionIndex] = (),
) -> list[str]:
    """Return every concrete route emitted for the selected project."""

    routes: set[str] = set()
    intro_prefix = "books/introductiontorealanalysisvolumei_jirilebl_2025/"
    for entry in entries:
        routes.add(entry.route)
        if entry.category == "books" and entry.stem == "book":
            routes.add(f"books/{entry.book_or_paper.lower()}/")
        elif entry.category == "papers" and entry.stem in {"paper", "main"}:
            routes.add(f"papers/{entry.book_or_paper.lower()}/")
        if entry.category == "books" and entry.route.startswith(
            intro_prefix + "chapters/chap00/"
        ):
            routes.add(entry.route[len(intro_prefix) :])
    for reader in reader_chapters:
        routes.add(reader.route)
        routes.update(reader.legacy_routes)
    routes.update(reader.route for reader in paper_readers)
    routes.update(index.route for index in paper_section_indexes)
    return sorted(routes)


def doc_link(module: str) -> str:
    return published_site_link(f"docs/ReasBook/{module.replace('.', '/')}.html")


def source_link(module: str) -> str:
    return repo_relative_link(f"ReasBook/{module.replace('.', '/')}.lean")


def chapter_source_link(e: Entry) -> str:
    chapter = f"Chap{e.chapter_num:02d}"
    return repo_relative_link(f"{chapter}/")


def paper_sections_source_link(e: Entry) -> str:
    _ = e
    return repo_relative_link("./")


def verso_link(route: str) -> str:
    return local_site_link(route)


def published_verso_link(route: str) -> str:
    return published_site_link(route)


def book_item_label(item: BookItem) -> str:
    kind = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", item.kind).strip()
    number = ".".join((str(item.chapter_num), *item.tail_parts))
    return f"{kind} {number}"


def paper_item_label(item: PaperItem) -> str:
    kind = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", item.kind).strip()
    number = ".".join((item.section_token, *item.tail_parts))
    return f"{kind} {number}"


# ---------------------------------------------------------------------------
# README and work-page writers
# ---------------------------------------------------------------------------


def write_book_readmes(source_root: Path, entries: list[Entry]) -> None:
    books_root = source_root / "Books"
    all_books = sorted([p.name for p in books_root.iterdir() if p.is_dir()])

    by_book: dict[str, list[Entry]] = {book: [] for book in all_books}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)

    for book in all_books:
        title = book_title(book)
        book_file = books_root / book / "Book.lean"
        item_entries = sorted(
            [
                e
                for e in by_book.get(book, [])
                if (e.section_num > 0 and e.part_num == 0)
            ],
            key=lambda e: (e.chapter_num, e.section_num, e.part_num, e.stem),
        )
        home_entry = next(
            (e for e in by_book.get(book, []) if e.stem == "book"),
            None,
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        if book in TBD_BOOKS:
            out.append("- Links: Verso (TBD) | Documentation (TBD) | Lean source (TBD)")
        else:
            verso_target = (
                published_verso_link(f"books/{book.lower()}/")
                if home_entry is not None
                else (
                    published_verso_link(item_entries[0].route)
                    if item_entries
                    else published_verso_link(f"books/{book.lower()}/")
                )
            )
            docs_target = published_site_link(
                f"docs/ReasBook/{project_docs_path(source_root, book, 'book')}.html"
            )
            links = [
                f"[Verso]({verso_target})",
                f"[Documentation]({docs_target})",
            ]
            if book_file.exists():
                links.append(f"[Lean source]({repo_relative_link('./')})")
            else:
                links.append("[Lean source](./)")
            out.append(f"- Links: {' | '.join(links)}")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no chapter/section modules discovered yet)")
            out.append("")
        else:
            current_chapter = None
            for e in item_entries:
                if current_chapter != e.chapter_num:
                    current_chapter = e.chapter_num
                    out.append(f"## {chapter_title_for_book(book, current_chapter)}")
                    out.append("")
                label = readme_label(e)
                if not label:
                    continue
                out.append(
                    f"- {label} "
                    f"([Verso]({published_verso_link(e.route)})) "
                    f"([Documentation]({doc_link(e.module)})) "
                    f"([Lean source]({chapter_source_link(e)}))"
                )
            out.append("")

        readme = books_root / book / "README.md"
        write_text_if_changed(readme, "\n".join(out), log=True)


def write_paper_readmes(source_root: Path, entries: list[Entry]) -> None:
    papers_root = source_root / "Papers"
    all_papers = sorted([p.name for p in papers_root.iterdir() if p.is_dir()])

    by_paper: dict[str, list[Entry]] = {paper: [] for paper in all_papers}
    for e in entries:
        if e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)

    for paper in all_papers:
        title = paper_title(paper)
        paper_file = papers_root / paper / "Paper.lean"
        item_entries = sorted(
            [
                e
                for e in by_paper.get(paper, [])
                if (e.section_num > 0 and e.part_num == 0)
            ],
            key=lambda e: (e.section_num, e.part_num, e.stem),
        )
        home_entry = next(
            (e for e in by_paper.get(paper, []) if e.stem in {"paper", "main"}),
            None,
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        verso_target = (
            published_verso_link(f"papers/{paper.lower()}/")
            if home_entry is not None
            else (
                published_verso_link(item_entries[0].route)
                if item_entries
                else published_verso_link(f"papers/{paper.lower()}/")
            )
        )
        docs_target = published_site_link(
            f"docs/ReasBook/{project_docs_path(source_root, paper, 'paper')}.html"
        )
        links = [
            f"[Verso]({verso_target})",
            f"[Documentation]({docs_target})",
        ]
        if paper_file.exists():
            links.append(f"[Lean source]({repo_relative_link('./')})")
        else:
            links.append("[Lean source](./)")
        out.append(f"- Links: {' | '.join(links)}")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no section modules discovered yet)")
            out.append("")
        else:
            out.append("## Sections")
            out.append("")
            for e in item_entries:
                label = readme_label(e)
                if not label:
                    continue
                out.append(
                    f"- {label} "
                    f"([Verso]({published_verso_link(e.route)})) "
                    f"([Documentation]({doc_link(e.module)})) "
                    f"([Lean source]({paper_sections_source_link(e)}))"
                )
            out.append("")

        readme = papers_root / paper / "README.md"
        write_text_if_changed(readme, "\n".join(out), log=True)


def write_root_readme(repo_root: Path, source_root: Path) -> None:
    readme_path = repo_root / "README.md"
    if not readme_path.exists():
        return

    lines = readme_path.read_text(encoding="utf-8").splitlines()
    changed = False

    def update_links_line(i: int, docs: str, lean_src: str, verso: str) -> None:
        nonlocal changed
        expected = "  - Links:"
        if i < 0 or i >= len(lines):
            return
        if not lines[i].startswith(expected):
            return
        new_line = f"  - Links: [Documentation]({docs}) | [Lean source]({lean_src}) | [Verso]({verso})"
        if lines[i] != new_line:
            lines[i] = new_line
            changed = True

    # Books block
    for book in sorted(
        [p.name for p in (source_root / "Books").iterdir() if p.is_dir()]
    ):
        if book in TBD_BOOKS:
            continue
        book_ref_re = re.compile(rf"/Books/{re.escape(book)}/?\)")
        book_repo_link = repo_relative_link(f"ReasBook/Books/{book}/")
        book_verso = published_verso_link(f"books/{book.lower()}/")
        has_book_agg = (source_root / "Books" / book / "Book.lean").exists()
        if has_book_agg:
            lean_src = repo_relative_link(f"ReasBook/Books/{book}/")
            docs_path = project_docs_path(source_root, book, "book")
            docs_link = published_site_link(f"docs/ReasBook/{docs_path}.html")
        else:
            lean_src = repo_relative_link(f"ReasBook/Books/{book}/")
            docs_link = published_site_link(f"docs/ReasBook/Books/{book}/")

        for i, line in enumerate(lines):
            if line.startswith("- [") and book_ref_re.search(line):
                repl = re.sub(
                    r"\((https?://[^)]+|\.?/[^)]+)\)$", f"({book_repo_link})", line
                )
                if repl != line:
                    lines[i] = repl
                    changed = True
                # Contributors line is usually i+1, links i+2
                for j in range(i + 1, min(i + 6, len(lines))):
                    if lines[j].startswith("  - Links:"):
                        update_links_line(j, docs_link, lean_src, book_verso)
                        break

    # Papers block
    for paper in sorted(
        [p.name for p in (source_root / "Papers").iterdir() if p.is_dir()]
    ):
        paper_ref_re = re.compile(rf"/Papers/{re.escape(paper)}/?\)")
        paper_repo_link = repo_relative_link(f"ReasBook/Papers/{paper}/")
        paper_verso = published_verso_link(f"papers/{paper.lower()}/")
        has_paper_agg = (source_root / "Papers" / paper / "Paper.lean").exists()
        if has_paper_agg:
            lean_src = repo_relative_link(f"ReasBook/Papers/{paper}/")
            docs_path = project_docs_path(source_root, paper, "paper")
            docs_link = published_site_link(f"docs/ReasBook/{docs_path}.html")
        else:
            lean_src = repo_relative_link(f"ReasBook/Papers/{paper}/")
            docs_link = published_site_link(f"docs/ReasBook/Papers/{paper}/")

        for i, line in enumerate(lines):
            if line.startswith("- [") and paper_ref_re.search(line):
                repl = re.sub(
                    r"\((https?://[^)]+|\.?/[^)]+)\)$", f"({paper_repo_link})", line
                )
                if repl != line:
                    lines[i] = repl
                    changed = True
                for j in range(i + 1, min(i + 6, len(lines))):
                    if lines[j].startswith("  - Links:"):
                        update_links_line(j, docs_link, lean_src, paper_verso)
                        break

    if changed:
        write_text_if_changed(readme_path, "\n".join(lines) + "\n", log=True)


def lean_module_name(s: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", s)


@lru_cache(maxsize=None)
def paper_documentation_modules(source_root: Path, paper: str) -> frozenset[str]:
    """Use the same public root and closure as the documentation builder."""
    from reasbook_build_sdk import library_target, plan_reachable_project_modules

    target = library_target(source_root, paper, "paper")
    return frozenset(entry.name for entry in
                     plan_reachable_project_modules(source_root, [target]).entries)


def statement_reading_links(source_root: Path, module: str, source_path: str,
                            category: str, project: str) -> str:
    source_link = f"([Lean source]({github_blob_link(source_path)}))"
    if category == "papers" and module not in paper_documentation_modules(source_root, project):
        return f"— source only (outside the published documentation root) {source_link}"
    docs_path = _module_to_docs_path(source_root, module)
    return (f"([Documentation]({portable_site_link(f'docs/ReasBook/{docs_path}.html')})) "
            + source_link)


def item_reading_links(source_root: Path, item: BookItem | PaperItem) -> str:
    """Do not send readers to a known imports-only placeholder item."""
    path = source_root.parent / item.source_path
    reading = source_reading(path.read_text(encoding="utf-8"))
    source_link = f"([Lean source]({github_blob_link(item.source_path)}))"
    external_roots = {"Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop"}
    if reading.imports_only and all(name.split('.')[0] in external_roots for name in reading.imports):
        return f"— no statement yet {source_link}"
    category, project = (('books', item.book) if isinstance(item, BookItem) else ('papers', item.paper))
    return statement_reading_links(source_root, item.module, item.source_path, category, project)


def item_anchor(item: BookItem | PaperItem) -> str:
    return item.stem.casefold().replace("_", "-")


def item_statement_blocks(source_root: Path, item: BookItem | PaperItem) -> list[str]:
    label = book_item_label(item) if isinstance(item, BookItem) else paper_item_label(item)
    path = source_root.parent / item.source_path
    source = path.read_text(encoding="utf-8")
    links = item_reading_links(source_root, item)
    if selection := ITEM_PREVIEWS.get(item.module):
        category, project = (('books', item.book) if isinstance(item, BookItem) else ('papers', item.paper))
        sources = project_sources(source_root, category, project)
        reachable = {name for name, _ in statement_sources(item.module, sources, follow_imports=True)}
        lines: list[str] = []
        for index, (module, declaration) in enumerate(selection, 1):
            target = sources.get(module)
            if target is None:
                raise ValueError(f"Selected statement source is missing: {item.module}: {module}")
            if module not in reachable:
                raise ValueError(f"Selected statement source is not imported: {item.module}: {module}")
            actual_source = target.relative_to(source_root.parent).as_posix()
            selected_links = statement_reading_links(source_root, module, actual_source, category, project)
            anchor = item_anchor(item) + (f"-clause-{index}" if index > 1 else "")
            lines.extend(statement_blocks(
                target.read_text(encoding="utf-8"), label, selected_links, anchor,
                declaration=declaration,
                note=f"Selected defining clause {index} of {len(selection)}; not the complete item."))
        return lines
    if statement_excerpts(source):
        return statement_blocks(source, label, links, item_anchor(item))
    category, project = (('books', item.book) if isinstance(item, BookItem) else ('papers', item.paper))
    targets = statement_sources(item.module, project_sources(source_root, category, project))
    if targets:
        name, target = next((target for target in targets if target[0].startswith(item.module + '.')), targets[0])
        actual_source = target.relative_to(source_root.parent).as_posix()
        links = statement_reading_links(source_root, name, actual_source, category, project)
        return statement_blocks(target.read_text(encoding="utf-8"), label, links, item_anchor(item))
    if "no statement yet" in links:
        return [f"- {label} {links}", ""]
    # Unknown/custom commands are not silently called an empty mathematical
    # item. Keep the anchor valid, with an honest indication of preview limits.
    return [f':::html div (id := {lean_string(item_anchor(item))})',
            f"{label} — statement preview unavailable {links}", ":::" , ""]


def statement_blocks(source: str, label: str, links: str, anchor: str,
                     *, limit: int | None = 1, declaration: str | None = None,
                     note: str = "") -> list[str]:
    """Render inert source excerpts with stable item anchors, never Lean proofs."""
    excerpts = statement_excerpts(source, label=label)
    if declaration is not None:
        matches = tuple(item for item in excerpts if item.name == declaration)
        if len(matches) != 1:
            raise ValueError(f"Selected statement must resolve exactly once: {label}: {declaration}")
        selected = matches
    else:
        selected = excerpts if limit is None else excerpts[:limit]
    if not excerpts:
        return [f"- {label} {links}", ""]
    # Verso requires outer directive fences to be wider than nested fences.
    lines = [f':::::html div (id := {lean_string(anchor)}) '
             '(«data-reasbook-statement» := "true") '
             '(«data-reasbook-verso-standalone» := "true")',
             '::::html div (class := "reader-statement-header")',
             ':::html div (class := "reader-statement-title") '
             '(role := "heading") («aria-level» := "3")',
             label, ':::',
             ':::html div (class := "reader-statement-links")',
             links, ':::', '::::', ""]
    if note:
        lines.extend([note, ""])
    for excerpt in selected:
        if excerpt.prose:
            # Treat upstream prose as text, not executable Verso directives.
            prose = ''.join(part if re.fullmatch(r'`[^`\n]+`', part)
                            else re.sub(r"([\\`*{}\[\]<>_#~$|])", r"\\\1", part)
                            for part in re.split(r'(`[^`\n]+`)', excerpt.prose))
            prose = " ".join(prose.split())
            if prose.startswith((':::', '%%%')):
                prose = '\\' + prose
            lines.extend([prose, ""])
        snippet = "\n".join((*excerpt.context, excerpt.signature))
        fence = "`" * max(3, 1 + max((len(run) for run in re.findall(r"`+", snippet)), default=0))
        lines.extend([fence, snippet, fence, ""])
    lines.extend([":::::" , ""])
    return lines


@lru_cache(maxsize=None)
def project_sources(source_root: Path, category: str, project: str) -> dict[str, Path]:
    directory = source_root / category.title() / project
    return {to_module(source_root, path): path for path in sorted(directory.rglob("*.lean"))}


def statement_sources(module: str, sources: dict[str, Path], *,
                      follow_imports: bool = False) -> list[tuple[str, Path]]:
    """Skip imports-only facades, staying inside the selected project."""
    found: list[tuple[str, Path]] = []
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visited or name not in sources:
            return
        visited.add(name)
        path = sources[name]
        text = path.read_text(encoding="utf-8")
        reading = source_reading(text)
        if statement_excerpts(text):
            found.append((name, path))
        if reading.imports_only or follow_imports:
            for child in reading.imports:
                visit(child)

    visit(module)
    return found


def module_statement_blocks(source_root: Path, module: str, category: str,
                            project: str, label: str, *, seen: set[str] | None = None,
                            limit: int | None = None) -> list[str]:
    lines: list[str] = []
    for name, path in statement_sources(module, project_sources(source_root, category, project)):
        if seen is not None:
            if name in seen:
                continue
            seen.add(name)
        source_path = path.relative_to(source_root.parent).as_posix()
        links = statement_reading_links(source_root, name, source_path, category, project)
        lines.extend(statement_blocks(path.read_text(encoding="utf-8"),
                                      label if name == module else module_label(name), links,
                                      name.casefold().replace(".", "-"), limit=limit))
    return lines


@lru_cache(maxsize=None)
def chapter_reading_modules(
    source_root: Path, reader: ReaderChapter,
) -> tuple[tuple[str, str, str, bool], ...]:
    """Share the exact file inventory between chapter content and navigation.

    Imports-only section facades resolve to their reading parts. Each rendered
    module occurs once, including when several facades import the same part.
    Empty sections remain visible as disabled, explicitly unfinished entries.
    """
    entries = {entry.module: entry for entry in reader.ordinary_sections}
    sources = project_sources(source_root, "books", reader.book)
    # A section facade may import numbered items; those already own a reader
    # card and must not acquire a second file entry under the section list.
    seen: set[str] = {item.module for item in reader.items}
    result: list[tuple[str, str, str, bool]] = []
    for source in sorted(reader.ordinary_section_modules,
                         key=lambda value: _natural_parts(tuple(re.split(r"(\d+)", value.relative_path)))):
        if source.module in seen:
            continue
        entry = entries.get(source.module)
        label = readme_label(entry) if entry else humanize_identifier(Path(source.relative_path).stem)
        targets = statement_sources(source.module, sources)
        if not targets:
            result.append((source.module, label, source.source_path, False))
            seen.add(source.module)
        for name, path in targets:
            if name not in seen:
                result.append((name, label if name == source.module else module_label(name),
                               path.relative_to(source_root.parent).as_posix(), True))
                seen.add(name)
    return tuple(result)


def write_work_pages(
    repo_root: Path,
    source_root: Path,
    entries: list[Entry],
    reader_chapters: Iterable[ReaderChapter] = (),
    paper_readers: Iterable[PaperReader] = (),
    paper_section_indexes: Iterable[PaperSectionIndex] = (),
    fragment_project: str | None = None,
) -> None:
    pages_root = repo_root / "ReasBookWeb" / "ReasBookSite" / "WorkPages"
    books_root = pages_root / "Books"
    papers_root = pages_root / "Papers"
    books_root.mkdir(parents=True, exist_ok=True)
    papers_root.mkdir(parents=True, exist_ok=True)

    readers = list(reader_chapters)
    item_paper_readers = list(paper_readers)
    section_indexes = list(paper_section_indexes)
    readers_by_book: dict[str, list[ReaderChapter]] = {}
    for reader in readers:
        readers_by_book.setdefault(reader.book, []).append(reader)

    expected_reader_pages: dict[Path, ReaderChapter] = {}
    for reader in readers:
        page_file = (
            books_root
            / lean_module_name(reader.book)
            / f"Chap{reader.chapter_num:02d}.lean"
        )
        previous = expected_reader_pages.get(page_file)
        if previous is not None:
            raise ValueError(
                "reader module path collision: "
                f"{previous.book}/{previous.chapter_num:02d} and "
                f"{reader.book}/{reader.chapter_num:02d}"
            )
        if page_file.exists():
            first_line = generated_body_first_line(page_file)
            if first_line != [GENERATED_READER_MARKER]:
                raise ValueError(
                    "refusing to overwrite non-generated chapter work page: "
                    f"{page_file}"
                )
        expected_reader_pages[page_file] = reader

    paper_readers_by_paper = {reader.paper: reader for reader in item_paper_readers}
    if len(paper_readers_by_paper) != len(item_paper_readers):
        raise ValueError("multiple item readers were generated for one paper")
    section_indexes_by_paper: dict[str, list[PaperSectionIndex]] = {}
    for index in section_indexes:
        section_indexes_by_paper.setdefault(index.paper, []).append(index)

    expected_paper_reader_pages: dict[Path, PaperReader] = {}
    for reader in item_paper_readers:
        page_file = papers_root / lean_module_name(reader.paper) / "Items.lean"
        expected_paper_reader_pages[page_file] = reader
        if page_file.exists():
            first_line = generated_body_first_line(page_file)
            if first_line != [GENERATED_PAPER_READER_MARKER]:
                raise ValueError(
                    "refusing to overwrite non-generated paper reader work page: "
                    f"{page_file}"
                )

    expected_section_index_pages: dict[Path, PaperSectionIndex] = {}
    for index in section_indexes:
        page_file = (
            papers_root
            / lean_module_name(index.paper)
            / f"Section{index.section_num:02d}.lean"
        )
        previous = expected_section_index_pages.get(page_file)
        if previous is not None:
            raise ValueError(
                "paper section index module path collision: "
                f"{previous.base.module} and {index.base.module}"
            )
        expected_section_index_pages[page_file] = index
        if page_file.exists():
            first_line = generated_body_first_line(page_file)
            if first_line != [GENERATED_PAPER_SECTION_MARKER]:
                raise ValueError(
                    "refusing to overwrite non-generated paper section work page: "
                    f"{page_file}"
                )

    by_book: dict[str, list[Entry]] = {}
    by_paper: dict[str, list[Entry]] = {}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)
        elif e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)
    for reader in readers:
        by_book.setdefault(reader.book, [])
    for reader in item_paper_readers:
        by_paper.setdefault(reader.paper, [])
    for index in section_indexes:
        by_paper.setdefault(index.paper, [])

    for book, b_entries in sorted(by_book.items()):
        title = book_title(book)
        section_entries = sorted(
            [e for e in b_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.stem),
        )
        module_name = lean_module_name(book)
        page_file = books_root / f"{module_name}.lean"

        lines: list[str] = []
        lines.append("import VersoBlog")
        lines.append("open Verso Genre Blog")
        lines.append("")
        lines.append(f"#doc (Page) {lean_string(title)} =>")
        lines.append("")
        docs_path = project_docs_path(source_root, book, "book")
        lines.append(':::html div (class := "reader-home-links")')
        lines.append(
            f"- [Documentation]({portable_site_link(f'docs/ReasBook/{docs_path}.html')})"
        )
        lines.append(
            f"- [Lean source]({github_tree_link(f'ReasBook/Books/{book}/')})"
        )
        lines.append(":::")
        lines.append("")
        book_readers = sorted(
            readers_by_book.get(book, []), key=lambda reader: reader.chapter_num
        )
        # Home is a compact chapter directory. File-level navigation belongs
        # in the sidebar and the chapter, not in a second all-items index here.
        chapters = {entry.chapter_num: entry.route
                    for entry in b_entries if is_chapter_entry(entry)}
        for reader in book_readers:
            chapters[reader.chapter_num] = reader.route
        if chapters:
            lines.append("# Chapters")
            lines.append("")
            lines.append(':::html div (class := "reader-chapter-grid")')
            for chapter_num, route in sorted(chapters.items()):
                lines.append(
                    f"- [Chapter {chapter_num:02d}]({portable_site_link(route)})"
                )
            lines.append(":::")
            lines.append("")
        # Retain access to reading sections lacking any chapter entry, without
        # duplicating chapters already represented above.
        section_entries = [entry for entry in section_entries if entry.chapter_num not in chapters]
        if section_entries:
            lines.append("# Section index:")
            lines.append("")
            current_chapter = None
            for e in section_entries:
                if current_chapter != e.chapter_num:
                    if current_chapter is not None:
                        lines.append("")
                    current_chapter = e.chapter_num
                    lines.append(f"## {chapter_title_for_book(book, current_chapter)}")
                    lines.append("")
                label = readme_label(e)
                if not label:
                    continue
                lines.append(f"- [{label}]({portable_site_link(e.route)})")
            lines.append("")
        if not section_entries and not chapters:
            lines.append("No separate reading sections are published for this version.")
            lines.append("")

        write_text_if_changed(page_file, "\n".join(lines), log=True)

    for reader in readers:
        chapter_items = reader.items
        page_file = (
            books_root
            / lean_module_name(reader.book)
            / f"Chap{reader.chapter_num:02d}.lean"
        )

        lines = [
            GENERATED_READER_MARKER,
            "-- Do not edit manually.",
            "import VersoBlog",
            "open Verso Genre Blog",
            "",
            "#doc (Page) "
            + lean_string(chapter_title_for_book(reader.book, reader.chapter_num))
            + " =>",
            "",
            ':::html div (class := "reader-chapter-links")',
            f"- [{book_title(reader.book)}]({portable_site_link(f'books/{reader.book.lower()}/')})",
            f"- [Lean source]({github_tree_link(reader.source_directory)})",
            ':::',
            "",
            ':::html div (class := "reader-scope-note")',
            "Proofs omitted. A `#check` excerpt shows the checked expression, not its inferred type.",
            ':::',
            "",
        ]
        if reader.ordinary_section_modules:
            lines.append("# Reading sections")
            lines.append("")
            for module, label, source_path, has_statement in chapter_reading_modules(source_root, reader):
                if has_statement:
                    links = statement_reading_links(source_root, module, source_path, "books", reader.book)
                    lines.extend(statement_blocks(
                        (source_root.parent / source_path).read_text(encoding="utf-8"), label, links,
                        module.casefold().replace(".", "-"), limit=None))
                else:
                    lines.append(f"- {label} — no statement yet "
                                 f"([Lean source]({github_blob_link(source_path)}))")
            lines.append("")
        by_section: dict[int, list[BookItem]] = {}
        for item in chapter_items:
            by_section.setdefault(item.section_num, []).append(item)
        for section_num, section_items in sorted(by_section.items()):
            section_title = (
                f"Section {reader.chapter_num}.{section_num}"
                if section_num > 0
                else "Statements"
            )
            lines.append(f"# {section_title}")
            lines.append("")
            for item in section_items:
                lines.extend(item_statement_blocks(source_root, item))
            lines.append("")
        if reader.support_modules:
            lines.append("# Supporting modules")
            lines.append("")
            lines.append(
                "These source modules support the indexed items and are listed "
                "separately so the chapter inventory remains complete."
            )
            lines.append("")
            for source in reader.support_modules:
                docs_path = _module_to_docs_path(source_root, source.module)
                lines.append(
                    f"- `{source.relative_path}` "
                    f"([Documentation]({portable_site_link(f'docs/ReasBook/{docs_path}.html')})) "
                    f"([Lean source]({github_blob_link(source.source_path)}))"
                )
            lines.append("")
        write_text_if_changed(page_file, "\n".join(lines), log=True)

    # Remove only files carrying our exact generated marker.  This keeps a
    # regenerated branch/fragment from retaining routes for deleted chapters,
    # while never touching hand-maintained work pages.
    if PROJECT_FRAGMENT:
        selected_book = (
            fragment_project.split("/", 1)[1]
            if fragment_project and fragment_project.startswith("books/")
            else ""
        )
        stale_candidates = (
            sorted((books_root / lean_module_name(selected_book)).glob("Chap*.lean"))
            if selected_book
            else []
        )
    else:
        stale_candidates = sorted(books_root.glob("*/Chap*.lean"))
    for candidate in stale_candidates:
        if candidate in expected_reader_pages:
            continue
        first_line = generated_body_first_line(candidate)
        if first_line == [GENERATED_READER_MARKER]:
            candidate.unlink()
            print(f"Removed stale generated page {candidate}")
            try:
                candidate.parent.rmdir()
            except OSError:
                pass

    for paper, p_entries in sorted(by_paper.items()):
        title = paper_title(paper)
        section_entries = sorted(
            [e for e in p_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.section_num, e.stem),
        )
        entry_points = sorted(
            [
                e
                for e in p_entries
                if e.section_num == 0
                and e.part_num == 0
            ],
            key=lambda e: (e.module.casefold(), e.stem),
        )
        module_name = lean_module_name(paper)
        page_file = papers_root / f"{module_name}.lean"

        lines: list[str] = []
        lines.append("import VersoBlog")
        lines.append("open Verso Genre Blog")
        lines.append("")
        lines.append(f"#doc (Page) {lean_string(title)} =>")
        lines.append("")
        docs_path = project_docs_path(source_root, paper, "paper")
        lines.append(':::html div (class := "reader-home-links")')
        lines.append(
            f"- [Documentation]({portable_site_link(f'docs/ReasBook/{docs_path}.html')})"
        )
        lines.append(
            f"- [Lean source]({github_tree_link(f'ReasBook/Papers/{paper}/')})"
        )
        lines.append(":::")
        lines.append("")
        item_reader = paper_readers_by_paper.get(paper)
        if item_reader is not None:
            lines.append("# Statements")
            lines.extend(["", ':::html div (class := "reader-scope-note")',
                          "Proofs omitted. A `#check` excerpt shows the checked expression, not its inferred type.", ':::'])
            lines.append("")
            for item in item_reader.items:
                lines.extend(item_statement_blocks(source_root, item))
            lines.append("")
        if section_entries:
            lines.append("Section index:")
            lines.append("")
            split_sections = {index.base.module: index for index in section_indexes_by_paper.get(paper, [])}
            for e in section_entries:
                label = readme_label(e)
                if not label:
                    continue
                split = split_sections.get(e.module)
                if split is not None:
                    for part in split.parts:
                        lines.append(f"- [{label} — Part {part.part_num}]({portable_site_link(part.route)})")
                else:
                    lines.append(f"- [{label}]({portable_site_link(e.route)})")
            lines.append("")
        elif entry_points and item_reader is None:
            lines.append("# Statements")
            lines.extend(["", ':::html div (class := "reader-scope-note")',
                          "Source excerpts; proofs omitted.", ':::'])
            lines.append("")
            seen_modules = set()
            for e in entry_points:
                stem = re.sub(r"(?<=\d)_(?=\d)", ".", e.module.rsplit(".", 1)[-1])
                label = humanize_identifier(stem)
                lines.extend(module_statement_blocks(source_root, e.module, "papers", paper, label,
                                                     seen=seen_modules, limit=1))
            lines.append("")

        write_text_if_changed(page_file, "\n".join(lines), log=True)

    for reader in item_paper_readers:
        page_file = papers_root / lean_module_name(reader.paper) / "Items.lean"
        lines = [
            GENERATED_PAPER_READER_MARKER,
            "-- Do not edit manually.",
            "import VersoBlog",
            "open Verso Genre Blog",
            "",
            f"#doc (Page) {lean_string(f'{paper_title(reader.paper)} -- Formalized items')} =>",
            "",
            f"- [Paper home]({portable_site_link(f'papers/{reader.paper.lower()}/')})",
            f"- [Lean source directory]({github_tree_link(reader.source_directory)})",
            "",
            f"This reader indexes {len(reader.items)} formalized items. "
            f"The source tree also contains {reader.support_module_count} supporting modules.",
            "",
        ]
        by_section: dict[str, list[PaperItem]] = {}
        for item in reader.items:
            by_section.setdefault(item.section_token, []).append(item)
        section_order = sorted(
            by_section,
            key=lambda token: (0, int(token))
            if token.isdigit()
            else (1, token.casefold()),
        )
        for section_token in section_order:
            heading = (
                f"Section {section_token}"
                if section_token.isdigit()
                else f"Appendix {section_token}"
            )
            lines.append(f"# {heading}")
            lines.append("")
            for item in by_section[section_token]:
                lines.extend(item_statement_blocks(source_root, item))
            lines.append("")
        write_text_if_changed(page_file, "\n".join(lines), log=True)

    for index in section_indexes:
        page_file = (
            papers_root
            / lean_module_name(index.paper)
            / f"Section{index.section_num:02d}.lean"
        )
        label = readme_label(index.base) or f"Section {index.section_num}"
        base_docs_path = _module_to_docs_path(source_root, index.base.module)
        lines = [
            GENERATED_PAPER_SECTION_MARKER,
            "-- Do not edit manually.",
            "import VersoBlog",
            "open Verso Genre Blog",
            "",
            f"#doc (Page) {lean_string(f'{paper_title(index.paper)} -- {label}')} =>",
            "",
            f"- [Paper home]({portable_site_link(f'papers/{index.paper.lower()}/')})",
            f"- [Parent documentation]({portable_site_link(f'docs/ReasBook/{base_docs_path}.html')})",
            f"- [Parent Lean source]({github_blob_link(index.source_path)})",
            "",
            "Statements from the reading parts (source excerpts; proofs omitted).",
            "",
            "# Parts",
            "",
        ]
        for part in index.parts:
            part_docs_path = _module_to_docs_path(source_root, part.module)
            source_file = paper_entry_source_file(source_root, part)
            if source_file is None:
                raise ValueError(f"paper part source disappeared: {part.module}")
            source_path = source_file.relative_to(source_root.parent).as_posix()
            lines.append(
                f"- Part {part.part_num} "
                f"([Reading page]({portable_site_link(part.route)})) "
                f"([Documentation]({portable_site_link(f'docs/ReasBook/{part_docs_path}.html')})) "
                f"([Lean source]({github_blob_link(source_path)}))"
            )
            lines.extend(module_statement_blocks(source_root, part.module, "papers", index.paper,
                                                 f"Part {part.part_num}"))
        lines.append("")
        write_text_if_changed(page_file, "\n".join(lines), log=True)

    if PROJECT_FRAGMENT:
        selected_paper = (
            fragment_project.split("/", 1)[1]
            if fragment_project and fragment_project.startswith("papers/")
            else ""
        )
        paper_dirs = (
            [papers_root / lean_module_name(selected_paper)] if selected_paper else []
        )
    else:
        paper_dirs = sorted(path for path in papers_root.iterdir() if path.is_dir())

    for paper_dir in paper_dirs:
        for candidate in sorted(paper_dir.glob("Items.lean")):
            if candidate in expected_paper_reader_pages:
                continue
            first_line = generated_body_first_line(candidate)
            if first_line == [GENERATED_PAPER_READER_MARKER]:
                candidate.unlink()
                print(f"Removed stale generated page {candidate}")
        for candidate in sorted(paper_dir.glob("Section*.lean")):
            if candidate in expected_section_index_pages:
                continue
            first_line = generated_body_first_line(candidate)
            if first_line == [GENERATED_PAPER_SECTION_MARKER]:
                candidate.unlink()
                print(f"Removed stale generated page {candidate}")
        try:
            paper_dir.rmdir()
        except OSError:
            pass


def write_home_page(repo_root: Path, entries: list[Entry], fragment_project: str | None = None) -> None:
    """Keep the generated release home focused on published reader paths."""

    home = repo_root / "ReasBookWeb" / "ReasBookSite" / "Home.lean"
    if fragment_project:
        category, project = fragment_project.split("/", 1)
        page = home.parent / "WorkPages" / category.title() / f"{lean_module_name(project)}.lean"
        content = page.read_text(encoding="utf-8")
        # Preserve Home's established authorship header; copy the actual project
        # body so its root has the same title/content, not a generic hub page.
        content = content[content.index("import VersoBlog"):]
        write_text_if_changed(home, content, log=False)
        return
    lines = [
        "-- This file is generated by scripts/gen_sections.py",
        "import VersoBlog",
        "open Verso Genre Blog",
        "",
        '#doc (Page) "ReasBook" =>',
        "",
        "Books and research papers formalized in Lean, with source-linked statements,",
        "documentation and theorem dependency maps.",
        "",
        f"- [Documentation]({portable_site_link('docs/')})",
        f"- [Theorem dependency maps]({portable_site_link('theorem-maps/')})",
        "",
    ]
    for category, project in sorted({(e.category, e.book_or_paper) for e in entries}):
        title = book_title(project) if category == "books" else paper_title(project)
        lines.append(f"- [{title}]({portable_site_link(f'{category}/{project.lower()}/')})")
    lines.append("")
    write_text_if_changed(home, "\n".join(lines), log=False)


def is_generated_overview_block(body_lines: list[str]) -> bool:
    lines = [line.strip() for line in body_lines if line.strip()]
    if not lines:
        return False
    first = lines[0]
    if not (
        first.startswith("Overview page for ") or re.match(r"^Chapter \d{2}$", first)
    ):
        return False
    return "Verso links:" in "\n".join(lines)


# ---------------------------------------------------------------------------
# Source overview maintenance
# ---------------------------------------------------------------------------


def upsert_overview_block(path: Path, body_lines: list[str]) -> None:
    orig_text = path.read_text(encoding="utf-8")
    text = orig_text
    old_block_pattern = re.compile(
        re.escape(OLD_OVERVIEW_BEGIN)
        + r"\n/-!.*?-/\n"
        + re.escape(OLD_OVERVIEW_END)
        + r"\n?",
        re.DOTALL,
    )
    text = old_block_pattern.sub("", text)
    text = re.sub(r"\n{3,}", "\n\n", text)

    lines = text.splitlines()

    # Remove auto-import marker comments from older generated files.
    lines = [
        line
        for line in lines
        if line.strip()
        not in {
            "-- BEGIN AUTO-IMPORTS (managed by orchestrator)",
            "-- END AUTO-IMPORTS",
        }
    ]

    insert_at = -1
    last_import = -1
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import = i
    insert_at = last_import + 1 if last_import >= 0 else 0

    while insert_at < len(lines) and lines[insert_at].strip() == "":
        insert_at += 1

    candidate_start = insert_at
    while candidate_start < len(lines) and lines[candidate_start].strip() == "":
        candidate_start += 1
    if candidate_start < len(lines) and lines[candidate_start].strip() == "/-!":
        candidate_end = None
        for j in range(candidate_start + 1, len(lines)):
            if lines[j].strip() == "-/":
                candidate_end = j
                break
        if candidate_end is not None:
            candidate_body = lines[candidate_start + 1 : candidate_end]
            if is_generated_overview_block(candidate_body):
                del lines[candidate_start : candidate_end + 1]
                while (
                    candidate_start < len(lines)
                    and lines[candidate_start].strip() == ""
                ):
                    if candidate_start == 0 or lines[candidate_start - 1].strip() == "":
                        del lines[candidate_start]
                    else:
                        break

    # Drop stale legacy docstring blocks used by old generated chapter aggregators.
    i = 0
    while i < len(lines):
        if lines[i].strip() == "/-!":
            j = i + 1
            while j < len(lines) and lines[j].strip() != "-/":
                j += 1
            if j < len(lines):
                block_text = "\n".join(lines[i + 1 : j])
                if "Auto-managed imports live below." in block_text:
                    del lines[i : j + 1]
                    while i < len(lines) and lines[i].strip() == "":
                        if i == 0 or lines[i - 1].strip() == "":
                            del lines[i]
                        else:
                            break
                    continue
        i += 1

    block_lines = ["/-!", *body_lines, "-/"]
    insert_lines = ["", *block_lines, ""]
    lines = lines[:insert_at] + insert_lines + lines[insert_at:]
    new_text = "\n".join(lines)
    new_text = re.sub(r"\n{3,}", "\n\n", new_text)
    if not new_text.endswith("\n"):
        new_text += "\n"

    if new_text != orig_text:
        path.write_text(new_text, encoding="utf-8")
        print(f"Updated overview in {path}")


def write_source_overviews(source_root: Path, entries: list[Entry]) -> None:
    book_entries = [e for e in entries if e.category == "books"]
    by_book: dict[str, list[Entry]] = {}
    for e in book_entries:
        by_book.setdefault(e.book_or_paper, []).append(e)

    for book, b_entries in sorted(by_book.items()):
        book_file = source_root / "Books" / book / "Book.lean"
        if not book_file.exists():
            continue
        book_module = _book_module(source_root, book, "Book")

        section_entries = sorted(
            [e for e in b_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.stem),
        )

        body: list[str] = []
        body.append(f"Overview page for {book_title(book)}.")
        body.append("")
        body.append(
            "This aggregation module imports the currently formalized sections in this book."
        )
        body.append(
            "Use the links below to jump directly into chapter and section overview pages."
        )
        body.append("")
        body.append("Verso links:")
        body.append(f"- [Book home]({portable_site_link(f'books/{book.lower()}/')})")
        body.append(
            f"- [Book overview]({portable_site_link(f'books/{book.lower()}/book/')})"
        )
        body.append("")
        if section_entries:
            body.append("Directory:")
            body.append("")
            current_chapter = None
            for e in section_entries:
                if current_chapter != e.chapter_num:
                    if current_chapter is not None:
                        body.append("")
                    current_chapter = e.chapter_num
                    body.append(f"{chapter_title_for_book(book, current_chapter)}")
                    body.append("")
                label = readme_label(e)
                if not label:
                    continue
                body.append(
                    f"- {label} ([Documentation]({docs_relative_doc_link(source_root, book_module, e.module)})) "
                    f"([Verso]({portable_site_link(e.route)}))"
                )
            body.append("")
        else:
            body.append("Directory: no section modules discovered yet.")
            body.append("")

        upsert_overview_block(book_file, body)

        by_chapter: dict[int, list[Entry]] = {}
        for e in section_entries:
            by_chapter.setdefault(e.chapter_num, []).append(e)

        for chapter_num, ch_entries in sorted(by_chapter.items()):
            chapter_file = source_root / "Books" / book / f"Chap{chapter_num:02d}.lean"
            if not chapter_file.exists():
                chapter_file.parent.mkdir(parents=True, exist_ok=True)
                imports = sorted({e.module for e in ch_entries})
                chapter_lines: list[str] = []
                for module in imports:
                    chapter_lines.append(f"import {module}")
                chapter_lines.append("")
                write_text_if_changed(
                    chapter_file,
                    "\n".join(chapter_lines),
                    log=False,
                )
                print(f"Wrote {chapter_file} (generated chapter aggregator)")

            chapter_route = f"books/{book.lower()}/chapters/chap{chapter_num:02d}/"
            chapter_title = chapter_title_for_book(book, chapter_num)
            chapter_module = _book_module(source_root, book, f"Chap{chapter_num:02d}")

            chapter_body: list[str] = []
            chapter_body.append(f"Chapter {chapter_num:02d}")
            chapter_body.append("")
            if chapter_title != f"Chapter {chapter_num:02d}":
                chapter_body.append(f"Title: {chapter_title}")
                chapter_body.append("")
            chapter_body.append(
                "This chapter aggregation page links to section overviews and source files."
            )
            chapter_body.append("")
            chapter_body.append("Verso links:")
            chapter_body.append(
                f"- [Chapter overview]({portable_site_link(chapter_route)})"
            )
            chapter_body.append(
                f"- [Book overview]({portable_site_link(f'books/{book.lower()}/book/')})"
            )
            chapter_body.append("")
            chapter_body.append("Section overviews:")
            chapter_body.append("")
            for e in sorted(ch_entries, key=lambda x: (x.section_num, x.stem)):
                label = readme_label(e)
                if not label:
                    continue
                chapter_body.append(
                    f"- {label} ([Documentation]({docs_relative_doc_link(source_root, chapter_module, e.module)})) "
                    f"([Verso]({portable_site_link(e.route)}))"
                )
            chapter_body.append("")

            upsert_overview_block(chapter_file, chapter_body)

    base_by_key: dict[tuple[str, int, int], Entry] = {}
    parts_by_key: dict[tuple[str, int, int], list[Entry]] = {}
    for e in book_entries:
        if e.section_num <= 0:
            continue
        key = (e.book_or_paper, e.chapter_num, e.section_num)
        if e.part_num == 0:
            base_by_key[key] = e
        else:
            parts_by_key.setdefault(key, []).append(e)

    for key, part_entries in sorted(parts_by_key.items()):
        base = base_by_key.get(key)
        if base is None:
            continue

        section_file = source_root / Path(*base.module.split(".")).with_suffix(".lean")
        if not section_file.exists():
            continue

        chapter_file = (
            source_root
            / "Books"
            / base.book_or_paper
            / f"Chap{base.chapter_num:02d}.lean"
        )
        chapter_route = (
            f"books/{base.book_or_paper.lower()}/chapters/chap{base.chapter_num:02d}/"
        )
        has_chapter_overview = chapter_file.exists()

        part_entries = sorted(part_entries, key=lambda e: (e.part_num, e.stem))
        section_label = readme_label(base) or section_title_from_stem(base.stem)

        body: list[str] = []
        body.append(f"Overview page for {section_label}.")
        body.append("")
        body.append(
            "This aggregation module imports all currently available part files for this section."
        )
        body.append("Use this page to jump to each part page quickly.")
        body.append("")
        body.append("Verso links:")
        body.append(f"- [Section overview]({portable_site_link(base.route)})")
        if has_chapter_overview:
            body.append(f"- [Chapter overview]({portable_site_link(chapter_route)})")
        body.append(
            f"- [Book overview]({portable_site_link(f'books/{base.book_or_paper.lower()}/book/')})"
        )
        body.append("")
        body.append("Directory:")
        body.append("")
        for p in part_entries:
            body.append(
                f"- Part {p.part_num} ([Documentation]({docs_relative_doc_link(source_root, base.module, p.module)})) "
                f"([Verso]({portable_site_link(p.route)}))"
            )
        body.append("")

        upsert_overview_block(section_file, body)


def main() -> None:
    args = parse_args()
    if args.repo_root is not None and args.repo_root_option is not None:
        positional = Path(args.repo_root).expanduser().resolve()
        option = Path(args.repo_root_option).expanduser().resolve()
        if positional != option:
            raise SystemExit(
                "repo root was provided twice with different values: "
                f"{positional} != {option}"
            )
    configured_root = args.repo_root_option or args.repo_root
    if configured_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    else:
        repo_root = Path(configured_root).resolve()

    source_root = repo_root / "ReasBook"
    web_root = repo_root / "ReasBookWeb"
    out_file = web_root / "ReasBookSite" / "Sections.lean"
    route_file = web_root / "ReasBookSite" / "RouteTable.lean"
    literate_manifest = web_root / ".literate-modules.json"
    fragment_manifest = web_root / ".project-fragment.json"

    if (
        not (source_root / "lakefile.lean").exists()
        and not (source_root / "lakefile.toml").exists()
    ):
        raise SystemExit(f"Lean project not found at {source_root}")

    try:
        fragment_project = validate_project_selection(source_root)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc

    if SKIP_MODULES:
        print(f"INFO: skipping {len(SKIP_MODULES)} module(s) from site generation")
        for mod in sorted(SKIP_MODULES):
            print(f"INFO:   skip module: {mod}")

    load_book_metadata_titles(source_root)
    chapter_inventories = collect_chapter_inventories(source_root)
    paper_inventories = collect_paper_inventories(source_root)
    entries = collect_entries(source_root, chapter_inventories, paper_inventories)
    # Fragment workers own generated web files only.  Source overviews and
    # repository READMEs are branch-wide catalog state and must never be
    # concurrently rewritten by one-project finalizers.
    if not PROJECT_FRAGMENT:
        write_source_overviews(source_root, entries)
        entries = collect_entries(source_root, chapter_inventories, paper_inventories)
    reader_chapters = collect_reader_chapters(entries, chapter_inventories)
    paper_readers = collect_paper_readers(paper_inventories)
    paper_section_indexes = collect_paper_section_indexes(source_root, entries)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    write_text_if_changed(out_file, emit_sections(entries, reader_chapters, source_root=source_root), log=False)
    write_text_if_changed(
        route_file,
        emit_route_table(
            entries,
            reader_chapters,
            paper_readers,
            paper_section_indexes,
        ),
        log=False,
    )
    write_text_if_changed(
        literate_manifest,
        emit_literate_manifest(entries),
        log=False,
    )
    if PROJECT_FRAGMENT:
        write_text_if_changed(
            fragment_manifest,
            json.dumps(
                {
                    "schema_version": 1,
                    "project": fragment_project,
                    "modules": [entry.module for entry in entries],
                    "routes": fragment_owned_routes(
                        entries,
                        reader_chapters,
                        paper_readers,
                        paper_section_indexes,
                    ),
                    "shared_catalog": False,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            log=False,
        )
    write_work_pages(
        repo_root,
        source_root,
        entries,
        reader_chapters,
        paper_readers,
        paper_section_indexes,
        fragment_project,
    )
    write_home_page(repo_root, entries, fragment_project)
    if not PROJECT_FRAGMENT:
        write_book_readmes(source_root, entries)
        write_paper_readmes(source_root, entries)
        write_root_readme(repo_root, source_root)
    else:
        print(f"Wrote isolated project fragment inputs for {fragment_project}")
    print(f"Wrote {out_file} with {len(entries)} sections")
    print(f"Wrote {route_file} with generated route macro")
    print(f"Wrote {literate_manifest} with {len(entries)} modules")
    if reader_chapters:
        item_count = sum(len(reader.items) for reader in reader_chapters)
        print(
            f"Wrote {len(reader_chapters)} compact chapter reader(s) "
            f"for {item_count} item-style module(s)"
        )
    if paper_readers:
        item_count = sum(len(reader.items) for reader in paper_readers)
        print(
            f"Wrote {len(paper_readers)} compact paper reader(s) "
            f"for {item_count} item-style module(s)"
        )
    if paper_section_indexes:
        print(
            f"Wrote {len(paper_section_indexes)} paper section index page(s) "
            "for imports-only parent modules"
        )


if __name__ == "__main__":
    main()
