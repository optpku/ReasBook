"""The legacy curated UI has literal items and templates, without data.json."""

import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

from reasbook_deploy_sdk.errors import DeployExecutionError
from reasbook_deploy_sdk.release.acceptance import ReleaseAcceptanceRunner


class CuratedMapAcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.project = SimpleNamespace(
            project_id="TR_LALM_theory",
            kind="papers",
            branch="v4.32.2",
            key="papers/TR_LALM_theory",
            commit="a" * 40,
            source_path="ReasBook/Papers/TR_LALM_theory",
        )
        self.script = """(function () {
          var ITEMS = [
            {id: "assumption-1", title: "A string containing key: and ];", dependencies: []},
            {id: "theorem-2", dependencies: ["assumption-1"]}
          ];
          document.title = "The active application";
        })();"""
        (self.root / "app.js").write_text(self.script)
        (self.root / "metadata.json").write_text(
            json.dumps(
                {
                    "generation": {"mode": "curated-static"},
                    "project": {
                        "id": "TR_LALM_theory",
                        "kind": "papers",
                        "branch": "v4.32.2",
                        "commit": "a" * 40,
                        "sourceRoot": "ReasBook/Papers/TR_LALM_theory/",
                    },
                    "nodes": 2,
                    "edges": 1,
                }
            )
        )
        (self.root / "index.html").write_text("""<html><body>
          <template id="statement-assumption-1">Assume regularity.</template>
          <template id="statement-theorem-2">The iterates converge.</template>
          <script src="./app.js"></script></body></html>""")

    def validate(self):
        ReleaseAcceptanceRunner._validate_theorem_map_content(self.root, self.project)

    def rejects(self):
        with self.assertRaises(DeployExecutionError):
            self.validate()

    def test_literal_items_with_readable_templates_are_accepted(self):
        self.validate()

    def test_empty_literal_is_rejected_despite_nonempty_metadata(self):
        (self.root / "app.js").write_text("var ITEMS = [];")
        self.rejects()

    def test_commented_out_items_do_not_count(self):
        (self.root / "app.js").write_text(
            "/*\n" + self.script + "\n*/\nvar ITEMS = [];"
        )
        self.rejects()

    def test_javascript_expressions_are_not_executed_or_accepted(self):
        (self.root / "app.js").write_text(
            'var ITEMS = [{id: "theorem-2", dependencies: computeDependencies()}];'
        )
        self.rejects()

    def test_missing_statement_template_is_rejected(self):
        (self.root / "index.html").write_text('<script src="./app.js"></script>')
        self.rejects()

    def test_computed_array_is_not_mistaken_for_literal_items(self):
        (self.root / "app.js").write_text(
            self.script.replace(
                "];\n          document.title",
                "].filter(() => false);\n          document.title",
            )
        )
        self.rejects()

    def test_metadata_count_mismatch_is_rejected(self):
        path = self.root / "metadata.json"
        metadata = json.loads(path.read_text())
        metadata["nodes"] = 24
        path.write_text(json.dumps(metadata))
        self.rejects()

    def test_unknown_dependency_is_rejected(self):
        (self.root / "app.js").write_text(
            self.script.replace('["assumption-1"]', '["missing"]')
        )
        self.rejects()

    def test_json_script_is_not_an_active_application(self):
        path = self.root / "index.html"
        path.write_text(
            path.read_text().replace(
                "<script src=", '<script type="application/json" src='
            )
        )
        self.rejects()

    def test_script_inside_template_is_not_active(self):
        path = self.root / "index.html"
        path.write_text(
            path.read_text().replace(
                '<script src="./app.js"></script>',
                '<template><script src="./app.js"></script></template>',
            )
        )
        self.rejects()

    def test_script_inside_noscript_is_not_active(self):
        path = self.root / "index.html"
        path.write_text(
            path.read_text().replace(
                '<script src="./app.js"></script>',
                '<noscript><script src="./app.js"></script></noscript>',
            )
        )
        self.rejects()

    def test_duplicate_template_cannot_hide_an_empty_first_template(self):
        path = self.root / "index.html"
        path.write_text(
            '<template id="statement-assumption-1"></template>' + path.read_text()
        )
        self.rejects()

    def test_stale_commit_is_rejected(self):
        self.project.commit = "b" * 40
        self.rejects()

    def test_wrong_source_root_is_rejected(self):
        self.project.source_path = "ReasBook/Papers/another_project"
        self.rejects()

    def test_empty_generic_data_does_not_fall_back_to_curated_items(self):
        (self.root / "data.json").write_text('{"items": []}')
        self.rejects()


if __name__ == "__main__":
    unittest.main()
