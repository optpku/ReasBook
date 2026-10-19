from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"


class GitHubWorkflowPolicyTests(unittest.TestCase):
    def test_release_pages_has_one_derived_input_and_scoped_permissions(self) -> None:
        text = (WORKFLOWS / "publish_release_pages.yml").read_text(encoding="utf-8")

        self.assertIn("release_tag:", text)
        self.assertIn("workflow_dispatch:", text)
        self.assertNotIn("  push:", text)
        self.assertNotIn("bundle_asset:", text)
        self.assertNotIn("bundle_sha256:", text)
        self.assertIn("permissions: {}", text)
        self.assertIn("      REASBOOK_PYTHON_BIN: python", text)
        self.assertIn("attestations: read", text)
        self.assertIn("pages: read", text)
        self.assertIn("pages: write", text)
        self.assertIn("id-token: write", text)
        self.assertIn("github-pages-production", text)
        self.assertIn("git/ref/tags/$RELEASE_TAG", text)
        self.assertIn("git/tags/$object_sha", text)
        self.assertIn('"$GITHUB_REF_TYPE" == branch', text)
        self.assertIn('"$GITHUB_REF_NAME" == "$default_branch"', text)
        self.assertIn("compare/$object_sha...$GITHUB_SHA", text)
        self.assertIn('"$comparison" == ahead', text)
        self.assertIn('"$object_sha" =~ ^[0-9a-f]{40}$', text)
        self.assertIn('echo "TAG_TARGET=$object_sha"', text)
        self.assertIn("release-manifest.json", text)
        self.assertIn("release-set.json", text)
        self.assertIn(".pages.site.tar.zst", text)
        self.assertIn('manifest.get("artifact") != "pages"', text)
        self.assertIn('manifest.get("base_path") != "/ReasBook/"', text)
        self.assertIn(
            'source.get("registry_commit") != os.environ["TAG_TARGET"]',
            text,
        )
        self.assertIn('source.get("tooling_revision")', text)
        self.assertIn(r"\+tooling-sha256:[0-9a-f]{64}", text)
        self.assertIn(
            "GitHub publication requires a clean commit-derived tooling revision",
            text,
        )
        self.assertIn('yaml.safe_load(Path("config/deploy/github-pages.yml").read_text())', text)
        self.assertIn('pages_policy["max_site_bytes"]', text)
        self.assertIn("1_000_000_000", text)
        self.assertIn("SHA256SUMS", text)
        self.assertIn("cmp .release/release-manifest.json", text)
        self.assertGreaterEqual(text.count('gh release verify "$RELEASE_TAG"'), 2)
        self.assertIn("gh release verify-asset", text)
        self.assertIn("GitHub CLI 2.93.0 or newer", text)
        self.assertIn("gh_major == 2 && gh_minor < 93", text)
        self.assertLess(
            text.index('gh_version="$(gh --version'),
            text.index('gh release verify "$RELEASE_TAG"'),
        )
        self.assertIn("for attempt in {1..12}; do", text)
        self.assertIn("if (( attempt < 12 )); then", text)
        self.assertIn("sleep 5", text)
        self.assertIn('[[ "$verified" -eq 1 ]]', text)
        self.assertNotIn("immutable-releases", text)
        self.assertLess(
            text.index("Verify immutable GitHub Release before download"),
            text.index("Download immutable release assets"),
        )
        self.assertLess(
            text.index("Download immutable release assets"),
            text.index("Verify immutable Release and downloaded asset attestations"),
        )
        self.assertIn("--profile github-pages", text)
        self.assertIn("--artifact-policy pages", text)
        self.assertNotIn("--max-site-files", text)
        self.assertNotIn("--max-site-bytes", text)
        self.assertNotIn("--max-archive-members", text)
        self.assertIn('stat -c %s ".release/$BUNDLE_ASSET"', text)
        self.assertIn("policy-digest --profile github-pages", text)
        self.assertIn('export TRUSTED_POLICY_SHA256="$trusted_policy"', text)
        self.assertIn(
            'release_set.get("artifact_policy_sha256") != trusted_policy',
            text,
        )
        self.assertIn("include-hidden-files: true", text)
        self.assertIn(
            "actions/upload-pages-artifact@"
            "fc324d3547104276b827a68afc52ff2a11cc49c9 # v5",
            text,
        )
        self.assertIn("actions/configure-pages@", text)
        self.assertIn("persist-credentials: false", text)
        self.assertIn(
            "python -m pip install --disable-pip-version-check --no-deps "
            "PyYAML==6.0.3",
            text,
        )
        self.assertNotIn("lake build", text)
        self.assertNotIn("lake exe", text)

        actions = re.findall(r"uses:\s*([^@\s]+)@([^\s#]+)", text)
        self.assertEqual(len(actions), 5)
        for action, revision in actions:
            with self.subTest(action=action):
                self.assertRegex(revision, r"^[0-9a-f]{40}$")

    def test_superseded_github_builders_are_removed(self) -> None:
        for name in ("deploy_pages.yml", "deploy_preview.yml", "docs_full.yml"):
            self.assertFalse((WORKFLOWS / name).exists(), name)

    def test_required_offline_check_runs_for_every_pull_request(self) -> None:
        text = (WORKFLOWS / "sdk_tests.yml").read_text(encoding="utf-8")

        self.assertIn("  pull_request: {}", text)
        self.assertEqual(text.count("    paths:"), 1)
        self.assertIn("      REASBOOK_PYTHON_BIN: python", text)


if __name__ == "__main__":
    unittest.main()
