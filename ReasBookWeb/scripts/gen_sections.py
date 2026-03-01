#!/usr/bin/env python3
"""Generate ReasBookSite/Sections.lean from the current ReasBook module tree."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import posixpath
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
import json


def parse_github_remote(url: str) -> tuple[str, str] | None:
    url = (url or "").strip()
    if not url:
        return None
    m = re.match(r"^https?://github\.com/([^/]+)/([^/]+?)(?:\.git)?/?$", url)
    if m:
        return m.group(1), m.group(2)
    m = re.match(r"^git@github\.com:([^/]+)/([^/]+?)(?:\.git)?/?$", url)
    if m:
        return m.group(1), m.group(2)
    return None


def parse_repo_slug(slug: str) -> tuple[str, str] | None:
    slug = (slug or "").strip().strip("/")
    if not slug or "/" not in slug:
        return None
    owner, repo = slug.split("/", 1)
    owner = owner.strip()
    repo = repo.strip()
    if not owner or not repo:
        return None
    return owner, repo


def git_output(args: list[str]) -> str:
    try:
        return subprocess.check_output(args, text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return ""


def git_config_get(key: str) -> str:
    return git_output(["git", "config", "--get", key])


def git_remote_url(name: str) -> str:
    if not name:
        return ""
    return git_config_get(f"remote.{name}.url")


def current_git_branch() -> str:
    return git_output(["git", "branch", "--show-current"])


def detect_default_branch() -> str:
    candidate_remotes: list[str] = []
    env_remote_name = os.environ.get("REASBOOK_GIT_REMOTE_NAME", "").strip()
    if env_remote_name:
        candidate_remotes.append(env_remote_name)

    branch = current_git_branch()
    if branch:
        branch_remote = git_config_get(f"branch.{branch}.remote")
        if branch_remote:
            candidate_remotes.append(branch_remote)

    push_default = git_config_get("remote.pushDefault")
    if push_default:
        candidate_remotes.append(push_default)

    for fallback in ("origin", "upstream"):
        candidate_remotes.append(fallback)

    seen: set[str] = set()
    for remote_name in candidate_remotes:
        if not remote_name or remote_name in seen:
            continue
        seen.add(remote_name)
        ref = git_output(["git", "symbolic-ref", "--quiet", "--short", f"refs/remotes/{remote_name}/HEAD"])
        prefix = f"{remote_name}/"
        if ref.startswith(prefix):
            branch_name = ref[len(prefix) :].strip()
            if branch_name:
                return branch_name
    return ""


def detect_github_repo() -> tuple[str, str]:
    for key in ("REASBOOK_GITHUB_REPO", "GITHUB_REPOSITORY"):
        parsed = parse_repo_slug(os.environ.get(key, ""))
        if parsed is not None:
            return parsed

    candidate_urls: list[str] = []

    env_remote_url = os.environ.get("REASBOOK_GIT_REMOTE_URL", "").strip()
    if env_remote_url:
        candidate_urls.append(env_remote_url)

    candidate_remotes: list[str] = []
    env_remote_name = os.environ.get("REASBOOK_GIT_REMOTE_NAME", "").strip()
    if env_remote_name:
        candidate_remotes.append(env_remote_name)

    branch = current_git_branch()
    if branch:
        branch_remote = git_config_get(f"branch.{branch}.remote")
        if branch_remote:
            candidate_remotes.append(branch_remote)

    push_default = git_config_get("remote.pushDefault")
    if push_default:
        candidate_remotes.append(push_default)

    for fallback in ("origin", "upstream"):
        candidate_remotes.append(fallback)

    seen: set[str] = set()
    for remote_name in candidate_remotes:
        if not remote_name or remote_name in seen:
            continue
        seen.add(remote_name)
        remote_url = git_remote_url(remote_name)
        if remote_url:
            candidate_urls.append(remote_url)

    for remote_url in candidate_urls:
        parsed = parse_github_remote(remote_url)
        if parsed is not None:
            return parsed

    return ("optsuite", "ReasBook")


def write_text_if_changed(path: Path, content: str, *, log: bool = True) -> bool:
    old_content: str | None
    try:
        old_content = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        old_content = None

    if old_content == content:
        return False

    path.write_text(content, encoding="utf-8")
    if log:
        print(f"Wrote {path}")
    return True


GITHUB_OWNER, GITHUB_REPO = detect_github_repo()
GITHUB_BRANCH = (
    os.environ.get("REASBOOK_GITHUB_BRANCH", "").strip()
    or os.environ.get("GITHUB_REF_NAME", "").strip()
    or detect_default_branch()
    or current_git_branch()
    or "main"
)

SITE_BASE = (
    os.environ.get("REASBOOK_SITE_BASE")
    or f"https://{GITHUB_OWNER}.github.io/{GITHUB_REPO}/"
).rstrip("/") + "/"

DEFAULT_SITE_ROOT = "/" if GITHUB_REPO == f"{GITHUB_OWNER}.github.io" else f"/{GITHUB_REPO}/"
SITE_ROOT = (os.environ.get("REASBOOK_SITE_ROOT") or DEFAULT_SITE_ROOT).strip()
if not SITE_ROOT.startswith("/"):
    SITE_ROOT = f"/{SITE_ROOT}"
if not SITE_ROOT.endswith("/"):
    SITE_ROOT = f"{SITE_ROOT}/"

DOCS_BASE = f"{SITE_BASE}docs/"

BOOK_TITLES = {
    "ConvexAnalysis_Rockafellar_1970": "Convex Analysis (Rockafellar, 1970)",
    "IntegerProgramming_Conforti_2014": "Integer Programming (Conforti et al., 2014)",
    "Analysis2_Tao_2022": "Analysis II (Tao, 2022)",
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": "Introduction to Real Analysis, Volume I (Jiri Lebl, 2025)",
}

PAPER_TITLES = {
    "SmoothMinimization_Nesterov_2004": "Smooth Minimization (Nesterov, 2004)",
    "OnSomeLocalRings_Maassaran_2025": "On Some Local Rings (Maassaran, 2025)",
}

# Temporary literate extraction bypass for pathological modules.
# Keep this list minimal and remove entries once upstream extraction is fixed.
DEFAULT_SKIP_MODULES = {
    "Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part12",
}


def parse_csv_env_set(name: str) -> set[str]:
    raw = (os.environ.get(name) or "").strip()
    if not raw:
        return set()
    return {item.strip() for item in raw.split(",") if item.strip()}


SKIP_MODULES = DEFAULT_SKIP_MODULES | parse_csv_env_set("REASBOOK_SKIP_MODULES")

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

TBD_BOOKS = {"IntegerProgramming_Conforti_2014"}

SKIP_STEMS = {"utils", "tactics", "scratch", "internal", "helper", "helpers"}

OLD_OVERVIEW_BEGIN = "-- BEGIN REASBOOK OVERVIEW (generated by scripts/gen_sections.py)"
OLD_OVERVIEW_END = "-- END REASBOOK OVERVIEW"

CHAPTER_RE = re.compile(r"^(?:chapter_|chap)(\d+)$", re.IGNORECASE)
SECTION_RE = re.compile(r"^section_?(\d+)$", re.IGNORECASE)
PART_RE = re.compile(r"^part_?(\d+)$", re.IGNORECASE)


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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "repo_root",
        nargs="?",
        default=None,
        help="Path to the ReasBook repo root (the directory containing ReasBookWeb/ and ReasBook/).",
    )
    return parser.parse_args()


def humanize_identifier(s: str) -> str:
    s = s.replace("_", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return s.title() if s else s


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
    if len(first.split()) > 8:
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
        section_titles = BOOK_SECTION_TITLES.get(e.book_or_paper, {}).get(e.chapter_num, {})
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
    if book in BOOK_TITLES:
        return BOOK_TITLES[book]
    return humanize_identifier(book)


def paper_title(paper: str) -> str:
    if paper in PAPER_TITLES:
        return PAPER_TITLES[paper]
    return humanize_identifier(paper)


def to_module(source_root: Path, path: Path) -> str:
    rel = path.relative_to(source_root)
    return ".".join(rel.with_suffix("").parts)


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


def docs_relative_doc_link(from_module: str, to_module: str) -> str:
    from_route = f"docs/{from_module.replace('.', '/')}.html"
    to_route = f"docs/{to_module.replace('.', '/')}.html"
    return route_relative_link(from_route, to_route)


def portable_site_link(route: str) -> str:
    norm = normalize_path(route)
    return f"{SITE_ROOT}{norm}" if norm else SITE_ROOT


def published_site_link(route: str) -> str:
    norm = normalize_path(route)
    return f"{SITE_BASE}{norm}" if norm else SITE_BASE


def should_include_book(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False

    if stem == "book":
        return True

    parts_lower = [p.lower() for p in path.parts]
    in_chapter_tree = any(CHAPTER_RE.match(p) for p in parts_lower) or (CHAPTER_RE.match(stem) is not None)
    if not in_chapter_tree:
        return False

    if stem.startswith("section"):
        return True

    return module_doc_title(path) is not None


def should_include_paper(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False
    if stem in {"paper", "main"}:
        return True
    return stem.startswith("section")


def collect_entries(source_root: Path) -> list[Entry]:
    entries: list[Entry] = []

    books_root = source_root / "Books"
    papers_root = source_root / "Papers"

    for path in sorted(books_root.rglob("*.lean")):
        if not should_include_book(path):
            continue
        module = to_module(source_root, path)
        if module in SKIP_MODULES:
            continue
        rel = path.relative_to(books_root)
        book = rel.parts[0]
        if book in TBD_BOOKS:
            continue
        ch_title = chapter_title(rel.parts)
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
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
        if not should_include_paper(path):
            continue
        module = to_module(source_root, path)
        if module in SKIP_MODULES:
            continue
        rel = path.relative_to(papers_root)
        paper = rel.parts[0]
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


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_sections(entries: list[Entry]) -> str:
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
                "title": chapter_title_for_book(book, chapter_num),
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
                    {"number": e.part_num, "title": f"Part {e.part_num}", "route": e.route}
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
                "title": entry_label(e) or section_title_from_stem(f"section{e.section_num:02d}"),
                "route": "",
                "parts": [],
            }
        section = sections[e.section_num]
        if e.part_num == 0:
            section["title"] = entry_label(e) or section["title"]
            section["route"] = e.route
        else:
            section["parts"].append({"number": e.part_num, "title": f"Part {e.part_num}", "route": e.route})

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
    lines.append(f"def docsRoot : String := {lean_string(local_site_link('docs/'))}")
    lines.append(f"def staticRoot : String := {lean_string(local_site_link('static/style.css'))}")
    lines.append("")
    lines.append(f"def sidebarDataJson : String := {lean_string(sidebar_json)}")
    lines.append("")
    lines.append("end ReasBookSite.Sections")
    lines.append("")
    return "\n".join(lines)


def emit_route_table(entries: list[Entry]) -> str:
    intro_book_slug = "introductiontorealanalysisvolumei_jirilebl_2025"

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

    work_page_imports = sorted(
        {
            work_page_module(e)
            for e in entries
            if (e.category == "books" and e.stem == "book")
            or (e.category == "papers" and e.stem in {"paper", "main"})
        }
    )

    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("import VersoBlog")
    lines.append("import ReasBookSite.Home")
    lines.append("import Book")
    for mod in work_page_imports:
        lines.append(f"import {mod}")
    lines.append("")
    lines.append("open Verso Genre Blog Site Syntax")
    lines.append("")
    lines.append("namespace ReasBookSite.RouteTable")
    lines.append("")
    lines.append("scoped syntax \"reasbook_site_dir\" : dir_spec")
    lines.append("")
    lines.append("macro_rules")
    lines.append("  | `(dir_spec| reasbook_site_dir) =>")
    lines.append("    `(dir_spec| /")
    lines.append('      static "static" ← "./static_files"')
    for e in entries:
        if e.category == "books" and e.stem == "book":
            target = work_page_module(e)
            lines.append(f'      "books/{e.book_or_paper.lower()}/" {target}')
            lines.append(f"      {lean_string(e.route)} {target}")
            continue
        if e.category == "papers" and e.stem in {"paper", "main"}:
            target = work_page_module(e)
            lines.append(f'      "papers/{e.book_or_paper.lower()}/" {target}')
            lines.append(f"      {lean_string(e.route)} {target}")
            continue
        target = f"Book.{e.module}"
        lines.append(f"      {lean_string(e.route)} {target}")
        for alias in alias_routes(e):
            lines.append(f"      {lean_string(alias)} {target}")
    lines.append("    )")
    lines.append("")
    lines.append("def reasbook_site : Site := site ReasBookSite.Home /")
    lines.append('  static "static" ← "./static_files"')
    for e in entries:
        if e.category == "books" and e.stem == "book":
            target = work_page_module(e)
            lines.append(f'  "books/{e.book_or_paper.lower()}/" {target}')
            lines.append(f"  {lean_string(e.route)} {target}")
            continue
        if e.category == "papers" and e.stem in {"paper", "main"}:
            target = work_page_module(e)
            lines.append(f'  "papers/{e.book_or_paper.lower()}/" {target}')
            lines.append(f"  {lean_string(e.route)} {target}")
            continue
        target = f"Book.{e.module}"
        lines.append(f"  {lean_string(e.route)} {target}")
        for alias in alias_routes(e):
            lines.append(f"  {lean_string(alias)} {target}")
    lines.append("")
    lines.append("end ReasBookSite.RouteTable")
    lines.append("")
    return "\n".join(lines)


def doc_link(module: str) -> str:
    return published_site_link(f"docs/{module.replace('.', '/')}.html")


def source_link(module: str) -> str:
    return repo_relative_link(f"ReasBook/{module.replace('.', '/')}.lean")


def chapter_source_link(e: Entry) -> str:
    chapter = f"Chap{e.chapter_num:02d}"
    return repo_relative_link(f"Chapters/{chapter}/")


def paper_sections_source_link(e: Entry) -> str:
    _ = e
    return repo_relative_link("Sections/")


def verso_link(route: str) -> str:
    return local_site_link(route)


def published_verso_link(route: str) -> str:
    return published_site_link(route)


def write_book_readmes(source_root: Path, entries: list[Entry]) -> None:
    books_root = source_root / "Books"
    all_books = sorted([p.name for p in books_root.iterdir() if p.is_dir()])

    by_book: dict[str, list[Entry]] = {book: [] for book in all_books}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)

    for book in all_books:
        title = book_title(book)
        book_module = f"Books.{book}.Book"
        book_file = books_root / book / "Book.lean"
        item_entries = sorted(
            [e for e in by_book.get(book, []) if (e.section_num > 0 and e.part_num == 0)],
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
            docs_target = doc_link(home_entry.module) if home_entry is not None else (
                doc_link(item_entries[0].module) if item_entries else doc_link(book_module)
            )
            links = [
                f"[Verso]({verso_target})",
                f"[Documentation]({docs_target})",
            ]
            if book_file.exists():
                links.append(f"[Lean source]({repo_relative_link('Chapters/')})")
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
        if paper_file.exists():
            paper_module = f"Papers.{paper}.Paper"
        else:
            paper_module = f"Papers.{paper}.Main"
        item_entries = sorted(
            [e for e in by_paper.get(paper, []) if (e.section_num > 0 and e.part_num == 0)],
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
        docs_target = doc_link(home_entry.module) if home_entry is not None else (
            doc_link(item_entries[0].module) if item_entries else doc_link(paper_module)
        )
        links = [
            f"[Verso]({verso_target})",
            f"[Documentation]({docs_target})",
        ]
        if paper_file.exists():
            links.append(f"[Lean source]({repo_relative_link('Sections/')})")
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
    for book in sorted([p.name for p in (source_root / "Books").iterdir() if p.is_dir()]):
        book_ref_re = re.compile(rf"/Books/{re.escape(book)}/?\)")
        book_repo_link = repo_relative_link(f"ReasBook/Books/{book}/")
        book_verso = published_verso_link(f"books/{book.lower()}/")
        has_book_agg = (source_root / "Books" / book / "Book.lean").exists()
        if has_book_agg:
            lean_src = repo_relative_link(f"ReasBook/Books/{book}/Chapters/")
            docs_link = published_site_link(f"docs/Books/{book}/Book.html")
        else:
            lean_src = repo_relative_link(f"ReasBook/Books/{book}/")
            docs_link = published_site_link(f"docs/Books/{book}/")

        for i, line in enumerate(lines):
            if line.startswith("- [") and book_ref_re.search(line):
                repl = re.sub(r"\((https?://[^)]+|\.?/[^)]+)\)$", f"({book_repo_link})", line)
                if repl != line:
                    lines[i] = repl
                    changed = True
                # Contributors line is usually i+1, links i+2
                for j in range(i + 1, min(i + 6, len(lines))):
                    if lines[j].startswith("  - Links:"):
                        update_links_line(j, docs_link, lean_src, book_verso)
                        break

    # Papers block
    for paper in sorted([p.name for p in (source_root / "Papers").iterdir() if p.is_dir()]):
        paper_ref_re = re.compile(rf"/Papers/{re.escape(paper)}/?\)")
        paper_repo_link = repo_relative_link(f"ReasBook/Papers/{paper}/")
        paper_verso = published_verso_link(f"papers/{paper.lower()}/")
        has_paper_agg = (source_root / "Papers" / paper / "Paper.lean").exists()
        if has_paper_agg:
            lean_src = repo_relative_link(f"ReasBook/Papers/{paper}/Sections/")
            docs_link = published_site_link(f"docs/Papers/{paper}/Paper.html")
        else:
            lean_src = repo_relative_link(f"ReasBook/Papers/{paper}/")
            docs_link = published_site_link(f"docs/Papers/{paper}/")

        for i, line in enumerate(lines):
            if line.startswith("- [") and paper_ref_re.search(line):
                repl = re.sub(r"\((https?://[^)]+|\.?/[^)]+)\)$", f"({paper_repo_link})", line)
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


def write_work_pages(repo_root: Path, source_root: Path, entries: list[Entry]) -> None:
    pages_root = repo_root / "ReasBookWeb" / "ReasBookSite" / "WorkPages"
    books_root = pages_root / "Books"
    papers_root = pages_root / "Papers"
    books_root.mkdir(parents=True, exist_ok=True)
    papers_root.mkdir(parents=True, exist_ok=True)

    by_book: dict[str, list[Entry]] = {}
    by_paper: dict[str, list[Entry]] = {}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)
        elif e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)

    for book, b_entries in sorted(by_book.items()):
        title = book_title(book)
        section_entries = sorted(
            [e for e in b_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.stem),
        )
        home_entry = next((e for e in b_entries if e.stem == "book"), None)
        module_name = lean_module_name(book)
        page_file = books_root / f"{module_name}.lean"
        book_dir = source_root / "Books" / book

        lines: list[str] = []
        lines.append("import VersoBlog")
        lines.append("open Verso Genre Blog")
        lines.append("")
        lines.append(f'#doc (Page) {lean_string(title)} =>')
        lines.append("")
        page_route = home_entry.route if home_entry is not None else f"books/{book.lower()}/"
        docs_path = (
            home_entry.module.replace(".", "/")
            if home_entry is not None
            else f"Books/{book}/Book"
        )
        lines.append(f"- [Documentation]({portable_site_link(f'docs/{docs_path}.html')})")
        if (book_dir / "Book.lean").exists():
            lines.append(f"- [Lean source path]({github_tree_link(f'ReasBook/Books/{book}/Chapters/')})")
        else:
            lines.append(f"- [Lean source path]({github_tree_link(f'ReasBook/Books/{book}/')})")
        lines.append("")
        if section_entries:
            lines.append("Section index:")
            lines.append("")
            current_chapter = None
            for e in section_entries:
                if current_chapter != e.chapter_num:
                    if current_chapter is not None:
                        lines.append("")
                    current_chapter = e.chapter_num
                    lines.append(f"{chapter_title_for_book(book, current_chapter)}")
                    lines.append("")
                label = readme_label(e)
                if not label:
                    continue
                lines.append(f"- [{label}]({portable_site_link(e.route)})")
            lines.append("")
        else:
            lines.append("- (TODO: no chapter/section modules discovered yet)")
            lines.append("")

        write_text_if_changed(page_file, "\n".join(lines), log=True)

    for paper, p_entries in sorted(by_paper.items()):
        title = paper_title(paper)
        section_entries = sorted(
            [e for e in p_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.section_num, e.stem),
        )
        home_entry = next((e for e in p_entries if e.stem in {"paper", "main"}), None)
        module_name = lean_module_name(paper)
        page_file = papers_root / f"{module_name}.lean"
        paper_dir = source_root / "Papers" / paper

        lines: list[str] = []
        lines.append("import VersoBlog")
        lines.append("open Verso Genre Blog")
        lines.append("")
        lines.append(f'#doc (Page) {lean_string(title)} =>')
        lines.append("")
        page_route = home_entry.route if home_entry is not None else f"papers/{paper.lower()}/"
        docs_path = (
            home_entry.module.replace(".", "/")
            if home_entry is not None
            else f"Papers/{paper}/Paper"
        )
        lines.append(f"- [Documentation]({portable_site_link(f'docs/{docs_path}.html')})")
        if (paper_dir / "Paper.lean").exists():
            lines.append(f"- [Lean source path]({github_tree_link(f'ReasBook/Papers/{paper}/Sections/')})")
        else:
            lines.append(f"- [Lean source path]({github_tree_link(f'ReasBook/Papers/{paper}/')})")
        lines.append("")
        if section_entries:
            lines.append("Section index:")
            lines.append("")
            for e in section_entries:
                label = readme_label(e)
                if not label:
                    continue
                lines.append(f"- [{label}]({portable_site_link(e.route)})")
            lines.append("")
        else:
            lines.append("- (TODO: no section modules discovered yet)")
            lines.append("")

        write_text_if_changed(page_file, "\n".join(lines), log=True)


def is_generated_overview_block(body_lines: list[str]) -> bool:
    lines = [line.strip() for line in body_lines if line.strip()]
    if not lines:
        return False
    first = lines[0]
    if not (first.startswith("Overview page for ") or re.match(r"^Chapter \d{2}$", first)):
        return False
    return "Verso links:" in "\n".join(lines)


def upsert_overview_block(path: Path, body_lines: list[str]) -> None:
    orig_text = path.read_text(encoding="utf-8")
    text = orig_text
    old_block_pattern = re.compile(
        re.escape(OLD_OVERVIEW_BEGIN) + r"\n/-!.*?-/\n" + re.escape(OLD_OVERVIEW_END) + r"\n?",
        re.DOTALL,
    )
    text = old_block_pattern.sub("", text)
    text = re.sub(r"\n{3,}", "\n\n", text)

    lines = text.splitlines()

    # Remove auto-import marker comments from older generated files.
    lines = [
        line
        for line in lines
        if line.strip() not in {
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
                while candidate_start < len(lines) and lines[candidate_start].strip() == "":
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
        book_module = f"Books.{book}.Book"

        section_entries = sorted(
            [e for e in b_entries if (e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.stem),
        )

        body: list[str] = []
        body.append(f"Overview page for {book_title(book)}.")
        body.append("")
        body.append("This aggregation module imports the currently formalized sections in this book.")
        body.append("Use the links below to jump directly into chapter and section overview pages.")
        body.append("")
        body.append("Verso links:")
        body.append(f"- [Book home]({portable_site_link(f'books/{book.lower()}/')})")
        body.append(f"- [Book overview]({portable_site_link(f'books/{book.lower()}/book/')})")
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
                    f"- {label} ([Documentation]({docs_relative_doc_link(book_module, e.module)})) "
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
            chapter_file = source_root / "Books" / book / "Chapters" / f"Chap{chapter_num:02d}.lean"
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
            chapter_module = f"Books.{book}.Chapters.Chap{chapter_num:02d}"

            chapter_body: list[str] = []
            chapter_body.append(f"Chapter {chapter_num:02d}")
            chapter_body.append("")
            if chapter_title != f"Chapter {chapter_num:02d}":
                chapter_body.append(f"Title: {chapter_title}")
                chapter_body.append("")
            chapter_body.append("This chapter aggregation page links to section overviews and source files.")
            chapter_body.append("")
            chapter_body.append("Verso links:")
            chapter_body.append(f"- [Chapter overview]({portable_site_link(chapter_route)})")
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
                    f"- {label} ([Documentation]({docs_relative_doc_link(chapter_module, e.module)})) "
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

        chapter_file = source_root / "Books" / base.book_or_paper / "Chapters" / f"Chap{base.chapter_num:02d}.lean"
        chapter_route = f"books/{base.book_or_paper.lower()}/chapters/chap{base.chapter_num:02d}/"
        has_chapter_overview = chapter_file.exists()

        part_entries = sorted(part_entries, key=lambda e: (e.part_num, e.stem))
        section_label = readme_label(base) or section_title_from_stem(base.stem)

        body: list[str] = []
        body.append(f"Overview page for {section_label}.")
        body.append("")
        body.append("This aggregation module imports all currently available part files for this section.")
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
                f"- Part {p.part_num} ([Documentation]({docs_relative_doc_link(base.module, p.module)})) "
                f"([Verso]({portable_site_link(p.route)}))"
            )
        body.append("")

        upsert_overview_block(section_file, body)


def main() -> None:
    args = parse_args()
    if args.repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    else:
        repo_root = Path(args.repo_root).resolve()

    source_root = repo_root / "ReasBook"
    out_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "Sections.lean"
    route_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "RouteTable.lean"

    if not (source_root / "lakefile.lean").exists() and not (source_root / "lakefile.toml").exists():
        raise SystemExit(f"Lean project not found at {source_root}")

    if SKIP_MODULES:
        print(f"INFO: skipping {len(SKIP_MODULES)} module(s) from site generation")
        for mod in sorted(SKIP_MODULES):
            print(f"INFO:   skip module: {mod}")

    entries = collect_entries(source_root)
    write_source_overviews(source_root, entries)
    entries = collect_entries(source_root)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    write_text_if_changed(out_file, emit_sections(entries), log=False)
    write_text_if_changed(route_file, emit_route_table(entries), log=False)
    write_work_pages(repo_root, source_root, entries)
    write_book_readmes(source_root, entries)
    write_paper_readmes(source_root, entries)
    write_root_readme(repo_root, source_root)
    print(f"Wrote {out_file} with {len(entries)} sections")
    print(f"Wrote {route_file} with generated route macro")


if __name__ == "__main__":
    main()
