"""Command line interface for theorem dependency graph generation."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .errors import TheoremGraphError
from .generator import GraphGenerator, TheoremGraphConfig
from .render import write_catalog


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="theorem-graph",
        description="Generate theorem dependency graph data and static pages.",
    )
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--site-root", type=Path, default=Path("ReasBookWeb/_site"))
    parser.add_argument("--branch", required=True)
    parser.add_argument("--repository", default="https://github.com/optpku/ReasBook")
    parser.add_argument("--extractor", type=Path)
    parser.add_argument("--assets", type=Path)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--compiled-root", type=Path)
    parser.add_argument(
        "--project",
        action="append",
        dest="project_keys",
        help="limit generation to books/ID or papers/ID (repeatable)",
    )
    parser.add_argument("--lake-bin")
    parser.add_argument(
        "--include-generic",
        action="store_true",
        help="generate maps for projects without a curated static map",
    )
    parser.add_argument(
        "--no-source-fallback",
        action="store_true",
        help="fail when compiled declaration extraction fails",
    )
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="skip compiled extraction and derive declarations from source comments",
    )
    parser.add_argument(
        "--no-replace",
        action="store_true",
        help="merge generated project directories into the existing output",
    )
    parser.add_argument("--commit", help="override the source commit recorded in JSON")
    parser.add_argument("--extractor-timeout-seconds", type=float, default=1800.0)
    parser.add_argument("--json", action="store_true", help="emit a JSON report")
    return parser


def _catalog_main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="theorem-graph catalog",
        description="Rebuild a catalog from already generated theorem maps.",
    )
    parser.add_argument("--site-root", type=Path, default=Path("ReasBookWeb/_site"))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    catalog = write_catalog(args.site_root.expanduser().resolve())
    if args.json:
        print(json.dumps({"catalog": str(catalog)}, ensure_ascii=True, indent=2))
    else:
        print(f"[theorem-graph] catalog: {catalog}")
    return 0


def main(argv: list[str] | None = None) -> int:
    values = list(sys.argv[1:] if argv is None else argv)
    if values and values[0] == "isolated":
        from .isolated import main as isolated_main

        try:
            return isolated_main(values[1:])
        except (TheoremGraphError, OSError, ValueError) as exc:
            print(f"[theorem-graph] error: {exc}", file=sys.stderr)
            return 2
    if values and values[0] == "catalog":
        try:
            return _catalog_main(values[1:])
        except (TheoremGraphError, OSError, ValueError) as exc:
            print(f"[theorem-graph] error: {exc}", file=sys.stderr)
            return 2
    args = build_parser().parse_args(values)
    try:
        repo_root = args.repo_root.expanduser().resolve()
        config = TheoremGraphConfig(
            repo_root=repo_root,
            site_root=args.site_root,
            branch=args.branch,
            repository=args.repository,
            extractor=args.extractor,
            assets=args.assets,
            source_root=args.source_root,
            compiled_root=args.compiled_root,
            lake_bin=args.lake_bin,
            commit=args.commit,
            extractor_timeout_seconds=args.extractor_timeout_seconds,
            include_generic=args.include_generic,
            fallback_to_source=not args.no_source_fallback,
            replace_output=not args.no_replace,
            project_keys=tuple(args.project_keys or ()),
            source_only=args.source_only,
        )
        def progress(event: object) -> None:
            print("[theorem-graph] " + json.dumps(event, ensure_ascii=False),
                  file=sys.stderr, flush=True)

        report = GraphGenerator(config, progress=progress).generate()
        if args.json:
            print(json.dumps(report.public_dict(), ensure_ascii=False, indent=2))
        else:
            print(
                f"[theorem-graph] generated {report.generated_count} of "
                f"{report.project_count} project maps"
            )
            print(f"[theorem-graph] output: {report.output_root}")
        return 0
    except (TheoremGraphError, OSError, ValueError) as exc:
        print(f"[theorem-graph] error: {exc}", file=sys.stderr)
        return 2


__all__ = ["build_parser", "main"]
