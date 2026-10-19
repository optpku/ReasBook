from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from reasbook_build_sdk.targets import (
    library_target,
    parse_library_declarations_text,
    parse_library_roots_text,
    project_doc_targets,
    selected_targets,
    target_from_declarations,
)


class ProjectTargetTests(unittest.TestCase):
    def test_remote_lake_source_resolves_targets_without_checkout(self) -> None:
        declarations = parse_library_declarations_text(
            'lean_lib Demo where\n  srcDir := "Books"\n'
        )
        self.assertEqual(
            target_from_declarations(declarations, "Demo", "book"),
            "Demo.Book",
        )

    def test_flat_layout_uses_project_entry_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "lakefile.lean").write_text(
                'lean_lib ZetaBook where\n  srcDir := "Books"\n'
                'lean_lib Analysis2_Tao_2022 where\n  srcDir := "Books"\n'
                'lean_lib SmoothMinimization_Nesterov_2004 where\n  srcDir := "Papers"\n',
                encoding="utf-8",
            )
            self.assertEqual(library_target(root, "ZetaBook"), "ZetaBook.Book")
            self.assertEqual(
                library_target(root, "Analysis2_Tao_2022"), "Analysis2_Tao_2022.Book"
            )
            self.assertEqual(
                project_doc_targets(root),
                [
                    "Analysis2_Tao_2022.Book",
                    "ZetaBook.Book",
                    "SmoothMinimization_Nesterov_2004.Paper",
                ],
            )
            self.assertEqual(
                selected_targets(
                    root, [{"kind": "books", "name": "Analysis2_Tao_2022"}]
                ),
                ["Analysis2_Tao_2022.Book:docs", "Analysis2_Tao_2022.Book"],
            )

    def test_aggregate_layout_uses_directory_module_names(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "lakefile.lean").write_text(
                "lean_lib Books where\n\nlean_lib Papers where\n",
                encoding="utf-8",
            )
            (root / "Books" / "Demo_Book").mkdir(parents=True)
            (root / "Papers" / "Demo_Paper").mkdir(parents=True)
            (root / "Books" / "Demo_Book" / "Book.lean").write_text(
                "", encoding="utf-8"
            )
            (root / "Papers" / "Demo_Paper" / "Paper.lean").write_text(
                "", encoding="utf-8"
            )

            self.assertEqual(library_target(root, "Demo_Book"), "Books.Demo_Book.Book")
            self.assertEqual(
                project_doc_targets(root),
                ["Books.Demo_Book.Book", "Papers.Demo_Paper.Paper"],
            )

    def test_explicit_roots_use_library_target(self) -> None:
        declarations = parse_library_declarations_text(
            "lean_lib TR_LALM_theory where\n"
            '  srcDir := "Papers"\n'
            "  roots := #[`TR_LALM_theory]\n"
        )
        roots = parse_library_roots_text(
            "lean_lib TR_LALM_theory where\n"
            '  srcDir := "Papers"\n'
            "  roots := #[`TR_LALM_theory]\n"
        )
        self.assertEqual(
            target_from_declarations(
                declarations, "TR_LALM_theory", "paper", roots=roots
            ),
            "TR_LALM_theory",
        )
        nested = parse_library_declarations_text(
            "lean_lib DFP_wolfe_local where\n"
            '  srcDir := "Papers"\n'
            "  roots := #[`DFP_wolfe_local.Paper]\n"
        )
        nested_roots = parse_library_roots_text(
            "lean_lib DFP_wolfe_local where\n"
            '  srcDir := "Papers"\n'
            "  roots := #[`DFP_wolfe_local.Paper]\n"
        )
        self.assertEqual(
            target_from_declarations(nested, "DFP_wolfe_local", "paper", roots=nested_roots),
            "DFP_wolfe_local.Paper",
        )


if __name__ == "__main__":
    unittest.main()
