from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]


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
