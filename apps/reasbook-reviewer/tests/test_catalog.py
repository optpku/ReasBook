from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_ROOT = PROJECT_ROOT.parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from catalog import catalog_payload, discover_books, discover_stacks_project, load_catalog, write_catalog  # noqa: E402


class CatalogTests(unittest.TestCase):
    def test_discovers_books_without_building_per_book_data(self) -> None:
        cache_root = PROJECT_ROOT / "data" / "books"
        before = sorted(str(path.relative_to(cache_root)) for path in cache_root.rglob("*") if path.is_file()) if cache_root.exists() else []
        records = discover_books(REPOSITORY_ROOT)
        after = sorted(str(path.relative_to(cache_root)) for path in cache_root.rglob("*") if path.is_file()) if cache_root.exists() else []

        self.assertEqual(len(records), 13)
        self.assertIn("analysis2_tao_2022", {record.slug for record in records})
        self.assertTrue(all(record.kind == "book" for record in records))
        self.assertTrue(all(record.review_index_state == "not-built" for record in records))
        self.assertTrue(all(record.item_count == 0 for record in records))
        self.assertEqual(before, after)

    def test_payload_is_portable_and_loadable(self) -> None:
        records = discover_books(REPOSITORY_ROOT)
        payload = catalog_payload(records, reasbook_root=REPOSITORY_ROOT)
        self.assertEqual(payload["source"]["root"], "ReasBook")
        renamed = catalog_payload(records, reasbook_root=Path("/private/operator-checkout"))
        self.assertEqual(renamed["source"], payload["source"])
        self.assertEqual(payload["cachePolicy"]["mode"], "on-demand")
        self.assertFalse(payload["cachePolicy"]["generated"])

        with tempfile.TemporaryDirectory() as temp_dir:
            target = Path(temp_dir) / "catalog.json"
            write_catalog(target, payload)
            loaded = load_catalog(target)
            self.assertEqual(target.stat().st_mode & 0o777, 0o644)
            self.assertEqual(list(target.parent.glob(".catalog.json*")), [])
        self.assertEqual(len(loaded["books"]), 13)

    def test_discovers_papers_when_requested(self) -> None:
        records = discover_books(REPOSITORY_ROOT, include_papers=True)
        papers = [record for record in records if record.kind == "paper"]

        self.assertEqual(len(papers), 4)
        self.assertEqual(
            {paper.slug for paper in papers},
            {
                "dfp_wolfe_local",
                "onsomelocalrings_maassaran_2025",
                "smoothminimization_nesterov_2004",
                "tr_lalm_theory",
            },
        )

    def test_stacks_project_is_an_optional_catalog_source(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "stacks_project").mkdir()
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
            with patch.dict("os.environ", {"REASBOOK_STACKS_ROOT": str(root)}):
                stacks = discover_stacks_project()
        self.assertIsNotNone(stacks)
        assert stacks is not None
        self.assertEqual(stacks.slug, "stacks_project")
        self.assertEqual(stacks.module_prefix, "stacks_project")
        self.assertEqual(stacks.source_repository, "Review")


if __name__ == "__main__":
    unittest.main()
