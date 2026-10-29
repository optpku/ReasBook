from __future__ import annotations

from pathlib import Path
import json
import re
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402
from reasbook_sdk_common.attribution import project_credits  # noqa: E402
from reasbook_sdk_common.catalog import catalog_page  # noqa: E402


def catalog(filename: str) -> dict[str, list[str]]:
    result = {}
    for line in (ROOT / filename).read_text(encoding="utf-8").splitlines():
        if not line.startswith("| **["):
            continue
        match = re.search(r"ReasBook/(Books|Papers)/([^/]+)/", line)
        if match:
            cells = line.split("|")
            if len(cells) != 6:
                raise AssertionError(f"Malformed catalog row: {line}")
            result[f"{match[1]}/{match[2]}"] = cells
    return result


def contributors(cell: str) -> list[str]:
    text = re.sub(r"<summary>.*?</summary>", "", cell)
    text = re.sub(r"<br\s*/?>", ", ", text)
    text = re.sub(r"<[^>]+>", "", text)
    text = re.sub(r"(?:Imported DFP infrastructure|导入的 DFP 基础库):\s*", "", text)
    return [name.strip() for name in text.split(",") if name.strip()]


class CatalogAttributionTests(unittest.TestCase):
    def test_reader_roster_covers_every_catalog_book_without_credit_drift(self) -> None:
        metadata = json.loads((ROOT / "sdk/common/src/reasbook_sdk_common/project_contributors.json").read_text())
        expected = {project.split("/", 1)[1]: contributors(cells[3])
                    for project, cells in catalog("README.md").items() if project.startswith("Books/")}
        self.assertEqual(metadata["scope"], "project")
        self.assertEqual(metadata["source"], "https://github.com/optpku/ReasBook/blob/main/README.md#books")
        self.assertEqual(metadata["books"], expected)
        for book, names in expected.items():
            blocks = "\n".join(generator.book_contributor_blocks(book))
            self.assertIn("Formalization contributors", blocks)
            self.assertIn(", ".join(names), blocks)
            self.assertIn("Project-level credit", blocks)
            self.assertNotIn("<details>", blocks, "published author names stay visible")
        self.assertEqual(generator.book_contributor_blocks("UnknownBook"), [])

    def test_shared_registry_covers_books_and_papers_preserving_roles(self) -> None:
        expected = {key[0].lower() + key[1:]: contributors(cells[3])
                    for key, cells in catalog("README.md").items()}
        credits = project_credits()
        self.assertEqual(expected.keys(), credits.keys())
        for key, credit in credits.items():
            names = [*credit.names, *(name for _, names in credit.additional for name in names)]
            self.assertEqual(names, expected[key])
            content = catalog_page("Collection", [(key, f"sites/{key.split('/')[1].lower()}/")])
            for name in names:
                self.assertIn(name, content)
            self.assertIn("Project-level credit", content)
        bfgs = credits["papers/BFGSMinimumQOrder_Liu_2026"]
        self.assertEqual(bfgs.names, ("Chenyi Li",))
        self.assertEqual(bfgs.additional, (("Imported DFP infrastructure", ("Zichen Wang",)),))
        self.assertIn("Imported DFP infrastructure: Zichen Wang",
                      '\n'.join(generator.project_contributor_blocks("papers/BFGSMinimumQOrder_Liu_2026")))

    def test_book_home_and_single_project_root_both_keep_project_credits(self) -> None:
        book = "FirstOrderMethodsOptimization_Beck_2017"
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = repo / "ReasBook"
            chapter = source / "Books" / book / "Chapters/Chap01"
            chapter.mkdir(parents=True)
            (source / "lakefile.lean").write_text(f'lean_lib {book} where\n  srcDir := "Books"\n')
            (chapter / "section01.lean").write_text('theorem example_thm : True := by trivial\n')
            entries = generator.collect_entries(source)
            generator.write_work_pages(repo, source, entries)
            generator.write_home_page(repo, entries, f"books/{book}")
            home = repo / f"ReasBookWeb/ReasBookSite/WorkPages/Books/{book}.lean"
            root_home = repo / "ReasBookWeb/ReasBookSite/Home.lean"
            for path in (home, root_home):
                content = path.read_text()
                self.assertEqual(content.count("# Formalization contributors"), 1)
                self.assertIn("Shu Miao, Zichen Wang, Zaiwen Wen", content)
                self.assertLess(content.index("Chapter 01"), content.index("# Formalization contributors"))

    def test_bilingual_catalog_credit_is_consistent_and_counts_actual_names(self) -> None:
        english, chinese = catalog("README.md"), catalog("README.zh-CN.md")
        self.assertEqual(english.keys(), chinese.keys())
        for project in english:
            with self.subTest(project=project):
                en, zh = contributors(english[project][3]), contributors(chinese[project][3])
                self.assertEqual(en, zh)
                self.assertEqual(len(en), len(set(en)))
                for cell in (english[project][3], chinese[project][3]):
                    count = re.search(r"<summary>(\d+)\s", cell)
                    if count:
                        self.assertEqual(int(count[1]), len(en))

    def test_confirmed_project_and_upstream_credits_are_not_lost(self) -> None:
        rows = catalog("README.md")
        beck = set(contributors(rows["Books/FirstOrderMethodsOptimization_Beck_2017"][3]))
        self.assertTrue({"Shu Miao", "Zichen Wang", "Zaiwen Wen", "Zhiyan Wang",
                         "Suwan Wu", "Changyu Zou", "Xinyi Guo", "Yunxi Duan", "Wanli Ma"} <= beck)
        self.assertIn("xdedlhqhw", contributors(rows["Books/ConvexAnalysis_Rockafellar_1970"][3]))
        bfgs = rows["Papers/BFGSMinimumQOrder_Liu_2026"][3]
        self.assertEqual(contributors(bfgs), ["Chenyi Li", "Zichen Wang"])
        self.assertIn("Imported DFP infrastructure:", bfgs)

    def test_vogel_source_availability_does_not_imply_release_publication(self) -> None:
        project = "Books/ComputationalMethodsInverseProblems_Vogel_2002"
        source = "https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/" + project + "/"
        for filename in ("README.md", "README.zh-CN.md"):
            cells = catalog(filename)[project]
            self.assertIn(source, cells[2])
            self.assertNotIn("http", cells[4])
        page = (ROOT / "ReasBook" / project / "README.md").read_text(encoding="utf-8")
        self.assertIn(source, page)
        self.assertIn("README.md#build", page)
        self.assertNotIn("Source: TBD", page)


if __name__ == "__main__":
    unittest.main()
