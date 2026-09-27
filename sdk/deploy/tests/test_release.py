from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from datetime import datetime, timezone
import io
import json
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from reasbook_sdk_common import CommandResult
from reasbook_deploy_sdk import DeployConfigError, DeployExecutionError
from reasbook_deploy_sdk.release.build_plan import (
    BranchPlanFactory,
    ReleaseBuildOptions,
)
from reasbook_deploy_sdk.release.bundle import (
    BundleVerifier,
    ReleaseBundler,
    _ArchiveMember,
    site_tree_digest,
)
from reasbook_deploy_sdk.release.cli import _main, build_parser
from reasbook_deploy_sdk.release.artifacts import (
    PagesSiteProjector,
    artifact_policy_digest,
    create_release_set,
)
from reasbook_deploy_sdk.release.config import (
    dump_profile_snapshot,
    load_canonical_projects,
    load_profile,
    load_registry,
)
from reasbook_deploy_sdk.release.models import (
    CanonicalProjects,
    DeploymentProfile,
    GITHUB_PAGES_HARD_SITE_BYTES,
    GitHubPublishProfile,
    ProjectSpec,
    ReleaseArtifactPolicy,
    RegistryBranch,
    ReleasePolicy,
    ReleaseSpec,
    SourceProject,
    ToolchainRegistry,
)
from reasbook_deploy_sdk.release.planner import ReleasePlanner
from reasbook_deploy_sdk.release.github import (
    GitHubPublication,
    GitHubReleasePublisher,
)
from reasbook_deploy_sdk.release.pages_config import GitHubPagesConfigurator
from reasbook_deploy_sdk.release.results import (
    BranchBuildResult,
    BundleInfo,
    ReleaseBuildReport,
    ReleasePackageResult,
    StageOutcome,
)
from reasbook_deploy_sdk.release.site import ReleaseSiteAssembler
from reasbook_deploy_sdk.release.service import (
    ReleaseContext,
    StaticReleaseService,
)
from reasbook_deploy_sdk.release.self_hosted import SelfHostedInstaller
from reasbook_deploy_sdk.release.source import _credential_free_remote
from reasbook_deploy_sdk.release.store import ReleaseLayout, ReleaseStore
from reasbook_deploy_sdk.release.tooling import (
    TOOLING_SNAPSHOT_ENTRIES,
    bind_tooling_revision,
    snapshot_ignore_for,
    tooling_digest_from_revision,
    tooling_source_digest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def release_manifest_fixture(
    release_id: str,
    *,
    artifact: str = "full",
    spec_digest: str | None = None,
    site_digest: str | None = None,
    file_count: int = 1,
    total_bytes: int = 7,
) -> dict:
    value = {
        "schema_version": 2,
        "release_id": release_id,
        "spec_digest": spec_digest or "sha256:" + "a" * 64,
        "artifact": artifact,
        "status": "success",
        "base_path": "/ReasBook/",
        "generated_at": "2026-09-01T14:00:00Z",
        "site_tree_sha256": site_digest or "sha256:" + "b" * 64,
        "file_count": file_count,
        "total_bytes": total_bytes,
        "projects": [],
        "branches": [],
    }
    return value


def github_pages_bundle_fixture(
    root: Path,
    release_id: str,
) -> tuple[BundleInfo, list[Path]]:
    """Create the four canonical, mutually bound Pages release assets."""

    spec_digest = "sha256:" + release_id.rsplit("-", 1)[-1] + "a" * 52
    site_digest = "sha256:" + "b" * 64
    bundle_path = root / f"{release_id}.pages.site.tar.zst"
    manifest_path = root / "release-manifest.json"
    manifest_path.write_text(
        json.dumps(
            release_manifest_fixture(
                release_id,
                artifact="pages",
                spec_digest=spec_digest,
                site_digest=site_digest,
            )
        ),
        encoding="utf-8",
    )
    archive_source = root / "archive-source"
    (archive_source / "site").mkdir(parents=True)
    shutil.copy2(manifest_path, archive_source / "release-manifest.json")
    (archive_source / "site" / "release-spec.json").write_text(
        "{}\n",
        encoding="utf-8",
    )
    (archive_source / "site" / "index.html").write_text(
        "fixture",
        encoding="utf-8",
    )
    subprocess.run(
        (
            "tar",
            "--zstd",
            "--create",
            "--file",
            str(bundle_path),
            "--directory",
            str(archive_source),
            "release-manifest.json",
            "site/release-spec.json",
            "site/index.html",
        ),
        check=True,
        capture_output=True,
        text=True,
    )
    digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
    checksums_path = root / "SHA256SUMS"
    checksums_path.write_text(
        f"{digest}  {bundle_path.name}\n",
        encoding="utf-8",
    )
    release_set_path = root / "release-set.json"
    release_set_path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "release_id": release_id,
                "spec_digest": spec_digest,
                "generated_at": "2026-09-01T14:00:00Z",
                "artifact_policy_sha256": "sha256:" + "c" * 64,
                "artifacts": [
                    {
                        "name": "full",
                        "bundle": f"{release_id}.site.tar.zst",
                        "bundle_sha256": "sha256:" + "d" * 64,
                        "site_tree_sha256": "sha256:" + "e" * 64,
                        "file_count": 2,
                        "total_bytes": 8,
                    },
                    {
                        "name": "pages",
                        "bundle": bundle_path.name,
                        "bundle_sha256": "sha256:" + digest,
                        "site_tree_sha256": site_digest,
                        "file_count": 1,
                        "total_bytes": 7,
                    },
                ],
            }
        ),
        encoding="utf-8",
    )
    assets = [bundle_path, manifest_path, checksums_path, release_set_path]
    return (
        BundleInfo(
            release_id,
            str(bundle_path),
            str(manifest_path),
            str(checksums_path),
            "sha256:" + digest,
            artifact="pages",
            release_set=str(release_set_path),
        ),
        assets,
    )


def github_release_assets(paths: list[Path] | tuple[Path, ...]) -> list[dict]:
    """Return the exact GitHub REST metadata for local release assets."""

    return [
        {
            "id": index,
            "name": path.name,
            "state": "uploaded",
            "size": path.stat().st_size,
            "digest": "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest(),
        }
        for index, path in enumerate(paths, start=100)
    ]


def accepted_release_set_sha256(bundle: BundleInfo) -> str:
    assert bundle.release_set is not None
    path = Path(bundle.release_set)
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


class FakeReleaseSource:
    def __init__(self) -> None:
        self.commits = {
            "v4.26.0": "a" * 40,
            "v4.30.0": "b" * 40,
        }
        self.projects = {
            "v4.26.0": (
                SourceProject("books", "Demo"),
                SourceProject("papers", "OnlyOld"),
            ),
            "v4.30.0": (SourceProject("books", "Demo"),),
        }
        self.fetch_count = 0

    def fetch(self) -> None:
        self.fetch_count += 1

    def repository_url(self) -> str:
        return "https://github.com/acme/reasbook.git"

    def registry_commit(self) -> str:
        return "c" * 40

    def tooling_revision(self) -> str:
        return "c" * 40

    def branch_commit(self, branch: str) -> str:
        return self.commits[branch]

    def read_text(self, branch: str, path: str) -> str:
        if path.endswith("lean-toolchain"):
            return f"leanprover/lean4:{branch}"
        if path.endswith("lake-manifest.json"):
            return json.dumps({"version": branch})
        if branch == "v4.26.0":
            return "lean_lib Books where\n\nlean_lib Papers where\n"
        return 'lean_lib Demo where\n  srcDir := "Books"\n'

    def discover_projects(self, branch: str):
        return self.projects[branch]


class RootedReleaseSource(FakeReleaseSource):
    """Minimal v4.32-style source with an explicit Lake root module."""

    def __init__(self) -> None:
        super().__init__()
        self.commits["v4.32.2"] = "d" * 40
        self.projects["v4.32.2"] = (SourceProject("papers", "TR_LALM_theory"),)

    def read_text(self, branch: str, path: str) -> str:
        if branch == "v4.32.2" and path.endswith("lakefile.lean"):
            return (
                "lean_lib TR_LALM_theory where\n"
                '  srcDir := "Papers"\n'
                "  roots := #[`TR_LALM_theory]\n"
            )
        return super().read_text(branch, path)


def profile(root: Path, *, historical: bool = True) -> DeploymentProfile:
    return DeploymentProfile(
        name="github-pages",
        registry=root / "toolchains.yml",
        canonical_projects=root / "canonical.yml",
        base_path="/ReasBook/",
        include_historical_versions=historical,
        policy=ReleasePolicy(),
        publish=GitHubPublishProfile(repository="acme/reasbook"),
    )


class ReleasePlanningTests(unittest.TestCase):
    def test_project_docs_copy_flat_entry_and_sibling_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            destination = root / "destination"
            docs = source / "docs" / "ReasBook"
            namespace = docs / "TR_LALM_theory"
            namespace.mkdir(parents=True)
            (docs / "TR_LALM_theory.html").write_text("entry", encoding="utf-8")
            (namespace / "Current.html").write_text("detail", encoding="utf-8")

            entry = PagesSiteProjector()._copy_project_docs(
                source,
                destination,
                "papers",
                "TR_LALM_theory",
                "TR_LALM_theory",
            )

            self.assertEqual(entry, Path("docs/ReasBook/TR_LALM_theory.html"))
            self.assertEqual(
                (destination / "docs/ReasBook/TR_LALM_theory.html").read_text(),
                "entry",
            )
            self.assertEqual(
                (
                    destination
                    / "docs/ReasBook/TR_LALM_theory/Current.html"
                ).read_text(),
                "detail",
            )

    def test_pages_route_score_prefers_indexed_landing_over_larger_fragment(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            landing = root / "books" / "demo"
            fragment = root / "demo"
            landing.mkdir(parents=True)
            (fragment / "chapter").mkdir(parents=True)
            (landing / "index.html").write_text(
                "<!doctype html><html></html>", encoding="utf-8"
            )
            (fragment / "chapter" / "index.html").write_text(
                "<!doctype html><html>" + ("large" * 10_000) + "</html>",
                encoding="utf-8",
            )

            self.assertGreater(
                PagesSiteProjector._verso_route_score(landing),
                PagesSiteProjector._verso_route_score(fragment),
            )

    def setUp(self) -> None:
        self.registry = ToolchainRegistry(
            (
                RegistryBranch("v4.26.0", "v4.26.0", "active"),
                RegistryBranch("v4.30.0", "v4.30.0", "active"),
                RegistryBranch("v4.32.0", "v4.32.0", "empty"),
            )
        )
        self.now = datetime(2026, 9, 1, 14, 0, tzinfo=timezone.utc)

    def test_explicit_canonical_produces_deterministic_immutable_spec(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            canonical = CanonicalProjects((("books/Demo", "v4.30.0"),))
            first = planner.resolve(profile(root), self.registry, canonical)
            second = planner.resolve(profile(root), self.registry, canonical)

            self.assertEqual(first.spec_digest, second.spec_digest)
            self.assertEqual(first.release_id, second.release_id)
            self.assertEqual(len(first.projects), 3)
            demo = [
                item
                for item in first.projects
                if item.key == "books/Demo" and item.canonical
            ]
            self.assertEqual([item.branch for item in demo], ["v4.30.0"])
            self.assertEqual(
                ReleaseSpec.from_dict(first.public_dict()),
                first,
            )

    def test_deployment_profile_rejects_unimplemented_artifact_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaisesRegex(DeployConfigError, "pages artifact"):
                DeploymentProfile(
                    name="github-pages",
                    registry=root / "toolchains.yml",
                    canonical_projects=root / "canonical.yml",
                    base_path="/ReasBook/",
                    include_historical_versions=True,
                    policy=ReleasePolicy(),
                    publish=GitHubPublishProfile(repository="acme/reasbook"),
                    artifacts=(
                        profile(root).artifact("full"),
                        ReleaseArtifactPolicy(
                            name="pages",
                            history_mode="full",
                            dependency_docs="full",
                            max_site_files=60_000,
                            max_site_bytes=850_000_000,
                            max_archive_members=180_000,
                            max_bundle_bytes=950_000_000,
                        ),
                    ),
                )

    def test_deployment_profile_rejects_pages_budget_above_github_hard_limit(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            default = profile(root)
            oversized_pages = replace(
                default.artifact("pages"),
                max_site_bytes=GITHUB_PAGES_HARD_SITE_BYTES + 1,
            )
            with self.assertRaisesRegex(DeployConfigError, "hard limit"):
                replace(
                    default,
                    artifacts=(default.artifact("full"), oversized_pages),
                )

    def test_pages_projection_applies_operational_and_hard_capacity_layers(
        self,
    ) -> None:
        projector = PagesSiteProjector(max_site_bytes=920_000_000)
        with self.assertRaisesRegex(DeployExecutionError, "budget is 920000000"):
            projector._validate_capacity(920_000_001)
        with self.assertRaisesRegex(DeployExecutionError, "hard limit is 1000000000"):
            projector._validate_capacity(GITHUB_PAGES_HARD_SITE_BYTES + 1)

    def test_external_api_classification_fails_closed_for_unknown_real_docs(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "Unknown" / "Page.html"
            source.parent.mkdir(parents=True)
            source.write_text("<!doctype html><html></html>", encoding="utf-8")
            unknown = Path("versions/v4.30.0/docs/ReasBook/Unknown/Page.html")
            mathlib = Path("versions/v4.30.0/docs/ReasBook/Mathlib/Page.html")

            self.assertFalse(
                PagesSiteProjector._is_external_api_doc(unknown, source)
            )
            self.assertTrue(
                PagesSiteProjector._is_external_api_doc(mathlib, source)
            )

            source.write_text(
                '<body data-reasbook-doc-stub="true"></body>',
                encoding="utf-8",
            )
            self.assertTrue(
                PagesSiteProjector._is_external_api_doc(unknown, source)
            )

    def test_doc_runtime_replaces_external_root_api_pages_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            destination = root / "destination"
            docs = source / "docs"
            reasbook_docs = docs / "ReasBook"
            reasbook_docs.mkdir(parents=True)

            external_pages = tuple(
                location / f"{namespace}.html"
                for location in (docs, reasbook_docs)
                for namespace in ("Mathlib", "Init", "Lean")
            )
            for page in external_pages:
                page.write_text(
                    f"<!doctype html><html><body>{page.stem}</body></html>",
                    encoding="utf-8",
                )

            runtime = docs / "search.html"
            runtime.write_bytes(b"runtime-search-page\n")
            project_owned = reasbook_docs / "Demo.html"
            project_owned.write_bytes(b"project-owned-api-root\n")

            PagesSiteProjector()._copy_doc_runtime(
                source,
                destination,
                "/ReasBook/",
            )

            for page in external_pages:
                projected = destination / page.relative_to(source)
                self.assertIn(
                    'data-reasbook-doc-stub="true"',
                    projected.read_text(encoding="utf-8"),
                )
                self.assertNotEqual(projected.read_bytes(), page.read_bytes())
            self.assertEqual(
                (destination / runtime.relative_to(source)).read_bytes(),
                runtime.read_bytes(),
            )
            self.assertEqual(
                (destination / project_owned.relative_to(source)).read_bytes(),
                project_owned.read_bytes(),
            )

    def test_pages_projection_rejects_encoded_parent_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            pages = Path(temp) / "pages"
            pages.mkdir()
            with self.assertRaisesRegex(DeployExecutionError, "unsafe internal"):
                PagesSiteProjector._resolve_missing_reference(
                    "https://reasbook.invalid",
                    "/ReasBook/",
                    "https://reasbook.invalid/ReasBook/index.html",
                    "/ReasBook/%2e%2e/private.txt",
                    pages,
                )

    def test_release_cli_exposes_portable_self_hosted_install(self) -> None:
        parsed = build_parser().parse_args(
            [
                "install",
                "/transfer/release.site.tar.zst",
                "--expected-bundle-sha256",
                "a" * 64,
                "--release-set",
                "/transfer/release-set.json",
                "--artifact-policy-sha256",
                "b" * 64,
                "--deploy-root",
                "/srv/reasbook",
                "--filesystem-health-only",
            ]
        )
        self.assertEqual(parsed.release_command, "install")
        self.assertEqual(parsed.deploy_root, Path("/srv/reasbook"))
        self.assertEqual(parsed.expected_bundle_sha256, "a" * 64)

        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--expected-bundle-sha256",
                    "a" * 64,
                    "--release-set",
                    "/transfer/release-set.json",
                    "--deploy-root",
                    "/srv/reasbook",
                    "--filesystem-health-only",
                ]
            )
        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--expected-bundle-sha256",
                    "",
                    "--release-set",
                    "/transfer/release-set.json",
                    "--artifact-policy-sha256",
                    "b" * 64,
                    "--deploy-root",
                    "/srv/reasbook",
                    "--filesystem-health-only",
                ]
            )
        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "install",
                    "/transfer/release.site.tar.zst",
                    "--expected-bundle-sha256",
                    "a" * 64,
                    "--release-set",
                    "/transfer/release-set.json",
                    "--artifact-policy-sha256",
                    "b" * 64,
                    "--deploy-root",
                    "/srv/reasbook",
                ]
            )

        build = build_parser().parse_args(
            ["build", "site-20260901T140000Z-" + "a" * 12]
        )
        self.assertEqual(build.max_parallel_branches, 3)
        self.assertEqual(build.docs_timeout_seconds, 43200.0)

        configured = build_parser().parse_args(
            [
                "configure-pages",
                "--profile",
                "github-pages",
                "--remove-policy-id",
                "202",
                "--expected-policy-name",
                "v4.30.0",
                "--expected-policy-type",
                "branch",
                "--dry-run",
            ]
        )
        self.assertEqual(configured.release_command, "configure-pages")
        self.assertTrue(configured.dry_run)
        self.assertEqual(configured.remove_policy_id, 202)
        self.assertEqual(configured.expected_policy_name, "v4.30.0")
        self.assertEqual(configured.expected_policy_type, "branch")
        self.assertEqual(configured.immutable_convergence_timeout_seconds, 300.0)
        self.assertEqual(configured.immutable_convergence_poll_seconds, 5.0)
        tuned = build_parser().parse_args(
            [
                "configure-pages",
                "--immutable-convergence-timeout-seconds",
                "420",
                "--immutable-convergence-poll-seconds",
                "7.5",
            ]
        )
        self.assertEqual(tuned.immutable_convergence_timeout_seconds, 420.0)
        self.assertEqual(tuned.immutable_convergence_poll_seconds, 7.5)
        with self.assertRaises(SystemExit):
            build_parser().parse_args(["configure-pages", "--remove-policy-id", "0"])
        for invalid in (
            ["--immutable-convergence-timeout-seconds", "0"],
            ["--immutable-convergence-timeout-seconds", "nan"],
            ["--immutable-convergence-poll-seconds", "0.5"],
            [
                "--immutable-convergence-timeout-seconds",
                "4",
                "--immutable-convergence-poll-seconds",
                "5",
            ],
        ):
            with self.subTest(invalid=invalid), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    build_parser().parse_args(["configure-pages", *invalid])

        release_id = "site-20260901T140000Z-" + "a" * 12
        parser = build_parser()
        self_hosted_commands = (
            [
                "publish",
                release_id,
                "--target",
                "self-hosted",
                "--deploy-root",
                "/srv/reasbook",
            ],
            [
                "rollback",
                "--to",
                release_id,
                "--target",
                "self-hosted",
                "--deploy-root",
                "/srv/reasbook",
            ],
        )
        for command in self_hosted_commands:
            error = io.StringIO()
            with self.subTest(command=command), redirect_stderr(error):
                with self.assertRaises(SystemExit):
                    parser.parse_args(command)
            self.assertIn("requires exactly one", error.getvalue())

        for health_mode in (
            ["--health-url", "http://127.0.0.1/ReasBook/release-spec.json"],
            ["--filesystem-health-only"],
        ):
            for command in self_hosted_commands:
                parsed_self_hosted = build_parser().parse_args([*command, *health_mode])
                self.assertEqual(parsed_self_hosted.target, "self-hosted")

        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            build_parser().parse_args(
                [
                    "publish",
                    release_id,
                    "--target",
                    "self-hosted",
                    "--health-url",
                    "http://127.0.0.1/ReasBook/release-spec.json",
                    "--filesystem-health-only",
                ]
            )

        help_output = io.StringIO()
        with redirect_stdout(help_output), self.assertRaises(SystemExit):
            build_parser().parse_args(["publish", "--help"])
        self.assertIn(
            "Required when --target self-hosted.",
            help_output.getvalue(),
        )

        digest = build_parser().parse_args(
            ["policy-digest", "--profile", "github-pages"]
        )
        self.assertEqual(digest.release_command, "policy-digest")
        self.assertEqual(digest.profile, "github-pages")

        verify = build_parser().parse_args(
            [
                "verify",
                "/transfer/release.site.tar.zst",
                "--max-site-files",
                "60000",
                "--max-site-bytes",
                "850000000",
                "--max-archive-members",
                "180000",
            ]
        )
        self.assertEqual(verify.max_site_files, 60_000)
        self.assertEqual(verify.max_site_bytes, 850_000_000)
        self.assertEqual(verify.max_archive_members, 180_000)
        profile_verify = build_parser().parse_args(
            [
                "verify",
                "/transfer/release.site.tar.zst",
                "--profile",
                "github-pages",
                "--artifact-policy",
                "pages",
            ]
        )
        self.assertEqual(profile_verify.profile, "github-pages")
        self.assertEqual(profile_verify.artifact_policy, "pages")
        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                ["verify", "/transfer/release.site.tar.zst", "--max-site-files", "0"]
            )

        with self.assertRaisesRegex(DeployConfigError, "plain YAML"):
            GitHubPublishProfile(
                repository="acme/reasbook",
                workflow="../untrusted.yml",
            )

    def test_configure_pages_cli_forwards_immutable_convergence_options(self) -> None:
        with (
            patch("reasbook_deploy_sdk.release.cli.GitHubPagesConfigurator") as factory,
            patch("reasbook_deploy_sdk.release.cli._print"),
        ):
            factory.return_value.configure.return_value = {"status": "configured"}
            self.assertEqual(
                _main(
                    [
                        "--repo-root",
                        str(REPO_ROOT),
                        "configure-pages",
                        "--immutable-convergence-timeout-seconds",
                        "420",
                        "--immutable-convergence-poll-seconds",
                        "7.5",
                    ]
                ),
                0,
            )
        factory.return_value.configure.assert_called_once_with(
            dry_run=False,
            remove_policy_id=None,
            expected_policy_name=None,
            expected_policy_type=None,
            immutable_convergence_timeout_seconds=420.0,
            immutable_convergence_poll_seconds=7.5,
        )

    def test_policy_digest_cli_reads_the_trusted_profile(self) -> None:
        profile_value = load_profile(
            REPO_ROOT / "config/deploy/github-pages.yml",
            repo_root=REPO_ROOT,
        )
        expected = artifact_policy_digest(profile_value.artifacts)
        self.assertEqual(
            profile_value.artifact("pages").max_archive_members,
            180_000,
        )
        self.assertEqual(
            profile_value.artifact("pages").max_site_bytes,
            920_000_000,
        )
        self.assertEqual(
            profile_value.artifact("full").max_archive_members,
            1_501_024,
        )
        with tempfile.TemporaryDirectory() as temp, patch(
            "reasbook_deploy_sdk.release.cli._print"
        ) as emit:
            status = _main(
                [
                    "--repo-root",
                    str(REPO_ROOT),
                    "--cache-root",
                    temp,
                    "policy-digest",
                    "--profile",
                    "github-pages",
                ]
            )
        self.assertEqual(status, 0)
        emit.assert_called_once_with(expected, as_json=False)

    def test_repository_identity_strips_embedded_credentials(self) -> None:
        self.assertEqual(
            _credential_free_remote("https://token@example.invalid/acme/reasbook.git"),
            "https://example.invalid/acme/reasbook.git",
        )

    def test_tooling_revision_is_deterministically_bound_to_tree_digest(self) -> None:
        digest = "d" * 64
        revision = bind_tooling_revision("abc+dirty:fingerprint", digest)

        self.assertEqual(tooling_digest_from_revision(revision), digest)
        self.assertEqual(
            revision,
            "abc+dirty:fingerprint+tooling-sha256:" + digest,
        )
        with self.assertRaisesRegex(DeployConfigError, "already bound"):
            bind_tooling_revision(revision, digest)

    def test_release_spec_requires_tooling_revision_from_registry_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec = self._spec(Path(temp))

            with self.assertRaisesRegex(
                DeployConfigError,
                "tooling_revision must derive from source.registry_commit",
            ):
                replace(spec, tooling_revision="d" * 40)

    def test_tooling_snapshot_ignores_sdk_packaging_outputs_by_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "repo"
            for sequence, relative in enumerate(TOOLING_SNAPSHOT_ENTRIES):
                directory = root / relative
                directory.mkdir(parents=True, exist_ok=True)
                (directory / f"source-{sequence}.txt").write_text(
                    f"source {sequence}\n", encoding="utf-8"
                )
            capability_source = (
                root / "sdk" / "build" / "src" / "reasbook_build_sdk" / "core.py"
            )
            capability_source.parent.mkdir(parents=True)
            capability_source.write_text("VALUE = 1\n", encoding="utf-8")
            clean_digest = tooling_source_digest(root)

            generated = (
                root / "sdk" / "build" / "build" / "lib" / "stale.py",
                root / "sdk" / "build" / "dist" / "stale.whl",
                root
                / "sdk"
                / "build"
                / "src"
                / "reasbook_build_sdk.egg-info"
                / "PKG-INFO",
                root / "sdk" / "deploy" / "build" / "lib" / "stale.py",
            )
            for path in generated:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"generated: {path.name}\n", encoding="utf-8")

            self.assertEqual(tooling_source_digest(root), clean_digest)
            copied = Path(temp) / "copied"
            shutil.copytree(
                root / "sdk",
                copied / "sdk",
                ignore=snapshot_ignore_for(root),
            )
            self.assertTrue((copied / capability_source.relative_to(root)).is_file())
            for path in generated:
                self.assertFalse((copied / path.relative_to(root)).exists())

    def test_duplicate_project_without_canonical_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            with self.assertRaisesRegex(
                DeployConfigError, "needs an explicit canonical"
            ):
                planner.resolve(
                    profile(Path(temp)),
                    self.registry,
                    CanonicalProjects(()),
                )

    def test_explicit_lake_root_is_used_for_release_target(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = RootedReleaseSource()
            registry = ToolchainRegistry(
                (RegistryBranch("v4.32.2", "v4.32.2", "active"),)
            )
            spec = ReleasePlanner(source, resolved_at=self.now).resolve(
                profile(root), registry, CanonicalProjects(())
            )
            self.assertEqual(spec.projects[0].build_target, "TR_LALM_theory")

    def test_historical_versions_can_be_omitted(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            planner = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now)
            spec = planner.resolve(
                profile(Path(temp), historical=False),
                self.registry,
                CanonicalProjects((("books/Demo", "v4.30.0"),)),
            )
            self.assertEqual(
                [(item.key, item.branch) for item in spec.projects],
                [
                    ("books/Demo", "v4.30.0"),
                    ("papers/OnlyOld", "v4.26.0"),
                ],
            )

    def test_canonical_selection_retains_version_qualified_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            configured = replace(profile(Path(temp)), selection_mode="canonical")
            spec = ReleasePlanner(FakeReleaseSource(), resolved_at=self.now).resolve(
                configured, self.registry,
                CanonicalProjects((("books/Demo", "v4.30.0"),)),
            )
            self.assertTrue(spec.include_historical_versions)
            self.assertTrue(all(p.canonical for p in spec.projects))
            self.assertEqual(len(spec.projects), 2)
            self.assertIn("mode: canonical", dump_profile_snapshot(configured))
            with self.assertRaises(DeployConfigError):
                replace(configured, selection_mode="unknown")

    def test_canonical_replacement_accepts_explicit_root_doc_file(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = ProjectSpec(
                key="papers/TR_LALM_theory",
                kind="papers",
                project_id="TR_LALM_theory",
                slug="tr_lalm_theory",
                branch="v4.32.2",
                commit="d" * 40,
                source_path="ReasBook/Papers/TR_LALM_theory",
                build_target="TR_LALM_theory",
                canonical=True,
                outputs=ReleasePolicy().outputs(),
            )
            monolith = root / "monolith"
            branch_site = root / "branch-site"
            source = branch_site / "docs" / "ReasBook" / "TR_LALM_theory.html"
            source.parent.mkdir(parents=True)
            source.write_text("root-doc", encoding="utf-8")

            ReleaseSiteAssembler._replace_canonical_project(
                monolith, branch_site, project
            )

            target = monolith / "docs" / "ReasBook" / "TR_LALM_theory.html"
            self.assertEqual(target.read_text(encoding="utf-8"), "root-doc")

    def test_site_publish_replaces_symlink_and_restores_on_rename_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            layout = ReleaseLayout(root / "cache", "site-20260901T140000Z-" + "a" * 12)
            assembler = ReleaseSiteAssembler(root, layout)
            layout.root.mkdir(parents=True)
            old = root / "old-site"
            old.mkdir()
            (old / "index.html").write_text("<html>old</html>", encoding="utf-8")
            layout.site.parent.mkdir(parents=True, exist_ok=True)
            layout.site.symlink_to(old, target_is_directory=True)

            staged = root / "staged"
            staged.mkdir()
            (staged / "index.html").write_text("<html>new</html>", encoding="utf-8")
            assembler._publish(staged)

            self.assertFalse(layout.site.is_symlink())
            self.assertEqual(
                (layout.site / "index.html").read_text(encoding="utf-8"),
                "<html>new</html>",
            )
            self.assertTrue(old.is_dir())

            # A failed second rename must put the original symlink back.
            shutil.rmtree(layout.site)
            layout.site.symlink_to(old, target_is_directory=True)
            staged = root / "staged-failure"
            staged.mkdir()
            (staged / "index.html").write_text("<html>failed</html>", encoding="utf-8")
            import reasbook_deploy_sdk.release.site as site_module

            real_replace = site_module.os.replace

            def fail_staged(source, destination):
                if Path(source) == staged:
                    raise OSError("injected rename failure")
                return real_replace(source, destination)

            with patch.object(site_module.os, "replace", side_effect=fail_staged):
                with self.assertRaises(OSError):
                    assembler._publish(staged)
            self.assertTrue(layout.site.is_symlink())
            self.assertEqual(layout.site.resolve(), old.resolve())

    def test_profile_registry_and_canonical_yaml_are_strictly_loaded(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            config = root / "config"
            config.mkdir()
            (config / "toolchains.yml").write_text(
                "schema_version: 1\n"
                "branches:\n"
                "  - version: v4.30.0\n"
                "    branch: v4.30.0\n"
                "    status: active\n",
                encoding="utf-8",
            )
            (config / "canonical.yml").write_text(
                "schema_version: 1\n" "books:\n" "  Demo: v4.30.0\n" "papers: {}\n",
                encoding="utf-8",
            )
            profile_path = config / "github-pages.yml"
            profile_path.write_text(
                "schema_version: 1\n"
                "name: github-pages\n"
                "registry: config/toolchains.yml\n"
                "canonical_projects: config/canonical.yml\n"
                "selection:\n"
                "  mode: all_active\n"
                "  exclude: [books/Broken]\n"
                "site:\n"
                "  base_path: /ReasBook/\n"
                "  include_historical_versions: true\n"
                "policy:\n"
                "  theorem_graph: compiled_or_source\n"
                "publish:\n"
                "  adapter: github_pages\n"
                "  repository: acme/reasbook\n",
                encoding="utf-8",
            )

            loaded = load_profile(profile_path, repo_root=root)
            self.assertEqual(loaded.exclude, ("books/Broken",))
            self.assertEqual(len(load_registry(loaded.registry).active()), 1)
            self.assertEqual(
                load_canonical_projects(loaded.canonical_projects).get("books/Demo"),
                "v4.30.0",
            )
            snapshot = root / "snapshot"
            snapshot.mkdir()
            (snapshot / "profile.yml").write_text(
                dump_profile_snapshot(loaded), encoding="utf-8"
            )
            (snapshot / "toolchains.yml").write_text(
                (config / "toolchains.yml").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            (snapshot / "canonical-projects.yml").write_text(
                (config / "canonical.yml").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            restored = load_profile(snapshot / "profile.yml", repo_root=snapshot)
            self.assertEqual(restored.publish, loaded.publish)

    def _spec(self, root: Path):
        return ReleasePlanner(FakeReleaseSource(), resolved_at=self.now).resolve(
            profile(root),
            self.registry,
            CanonicalProjects((("books/Demo", "v4.30.0"),)),
        )

    def _self_hosted_package(
        self,
        root: Path,
        *,
        generated_at: datetime | None = None,
        content: str = "site",
    ):
        at = generated_at or self.now
        spec = ReleasePlanner(FakeReleaseSource(), resolved_at=at).resolve(
            profile(root),
            self.registry,
            CanonicalProjects((("books/Demo", "v4.30.0"),)),
        )
        layout = ReleaseLayout(root / "cache", spec.release_id)
        store = ReleaseStore(layout)
        store.initialize(spec)
        layout.site.mkdir()
        (layout.site / "index.html").write_text(content, encoding="utf-8")
        (layout.site / "release-spec.json").write_text(
            json.dumps(spec.public_dict()),
            encoding="utf-8",
        )
        report = ReleaseBuildReport.from_branches(
            spec,
            tuple(
                BranchBuildResult(
                    branch.name,
                    branch.commit,
                    "success",
                    str(root / branch.name),
                    (StageOutcome("fixture", "success"),),
                )
                for branch in spec.branches
            ),
        )
        bundler = ReleaseBundler(layout, store, generated_at=at)
        full = bundler.package(spec, report)
        shutil.copytree(layout.site, layout.pages_site)
        pages = bundler.package_pages(
            spec,
            report,
            policy=profile(root).artifact("pages"),
        )
        _release_set, bundles = create_release_set(
            layout,
            store,
            spec,
            profile(root).artifacts,
            (full, pages),
        )
        full = next(item for item in bundles if item.artifact == "full")
        return spec, full, layout.release_set, layout

    @staticmethod
    def _write_raw_bundle(package_root: Path, bundle: Path, *extra: str) -> None:
        subprocess.run(
            (
                "tar",
                "--zstd",
                "-cf",
                str(bundle),
                *extra,
                "-C",
                str(package_root),
                "site",
                "release-manifest.json",
            ),
            check=True,
            capture_output=True,
            text=True,
        )

    def test_branch_plan_is_ordered_and_uses_isolated_runtime_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            branch = spec.branch("v4.26.0")
            worktree = root / "worktree"
            worktree.mkdir()
            plan = BranchPlanFactory(
                REPO_ROOT,
                root / "cache",
                layout,
                ReleaseBuildOptions(),
            ).create(spec, branch, worktree)

            self.assertEqual(
                [step.name for step in plan.steps],
                [
                    "cache",
                    "lean",
                    "docs",
                    "verso",
                    "publish-docs",
                    "theorem-graph",
                ],
            )
            environment = dict(plan.steps[0].env)
            self.assertIn(
                spec.branch("v4.26.0").commit[:12],
                environment["REASBOOK_RUNTIME_CACHE_PREFIX"],
            )
            self.assertEqual(
                environment["REASBOOK_SITE_ROOT"],
                "/ReasBook/versions/v4.26.0/",
            )
            self.assertEqual(
                environment["REASBOOK_DOC_SOURCE"],
                environment["REASBOOK_DOC_BUILD_DIR"] + "/doc",
            )
            self.assertIn("Demo.Book", environment["REASBOOK_LAKE_TARGETS"])

    def test_release_store_and_bundle_round_trip(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            with self.assertRaisesRegex(DeployExecutionError, "another release"):
                store.write_build_report(
                    ReleaseBuildReport(
                        "site-20260901T140000Z-" + "0" * 12,
                        spec.spec_digest,
                        "success",
                        (),
                    )
                )
            branch_sites = {
                "v4.26.0": root / "site-426",
                "v4.30.0": root / "site-430",
            }
            self._write_branch_site(
                branch_sites["v4.26.0"],
                books={"Demo": "old"},
                papers={"OnlyOld": "paper"},
            )
            self._write_branch_site(
                branch_sites["v4.30.0"],
                books={"Demo": "canonical"},
                papers={},
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(branch_sites[branch.name]),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            store.write_build_report(report)
            ReleaseSiteAssembler(REPO_ROOT, layout).assemble(spec, report)
            store.transition("validated", completed_stage="site")

            canonical_doc = layout.site / "sites" / "demo" / "docs" / "Book.html"
            canonical_redirect = canonical_doc.read_text(encoding="utf-8")
            self.assertIn('http-equiv="refresh"', canonical_redirect)
            self.assertIn(
                "docs/ReasBook/Books/Demo/Book.html",
                canonical_redirect,
            )
            self.assertEqual(
                (
                    layout.site
                    / "versions"
                    / "v4.30.0"
                    / "docs"
                    / "ReasBook"
                    / "Books"
                    / "Demo"
                    / "Book.html"
                ).read_text(encoding="utf-8"),
                "<!doctype html><html><body>canonical</body></html>",
            )
            self.assertTrue(
                (layout.site / "versions" / "v4.26.0" / "index.html").is_file()
            )
            self.assertIn(
                "https://github.com/optpku/ReasBook#readme",
                (layout.site / "index.html").read_text(encoding="utf-8"),
            )
            self.assertNotIn(
                "Version Archive",
                (layout.site / "index.html").read_text(encoding="utf-8"),
            )
            bundler = ReleaseBundler(
                layout,
                store,
                generated_at=self.now,
            )
            bundle = bundler.package(spec, report)
            repeated = bundler.package(spec, report)
            self.assertEqual(bundle.bundle_sha256, repeated.bundle_sha256)
            with self.assertRaisesRegex(DeployConfigError, "SHA-256"):
                BundleVerifier().inspect(
                    Path(bundle.bundle),
                    expected_sha256="",
                )
            self.assertNotIn(
                str(root),
                layout.manifest.read_text(encoding="utf-8"),
            )
            extracted = root / "extracted"
            manifest = BundleVerifier().verify(
                Path(bundle.bundle),
                expected_sha256=bundle.bundle_sha256,
                extract_to=extracted,
            )
            self.assertEqual(manifest.release_id, spec.release_id)
            self.assertTrue((extracted / "index.html").is_file())
            self.assertEqual(
                ReleaseStore.find_by_digest(root / "cache", spec.spec_digest),
                spec,
            )

    def test_release_set_packages_slim_pages_and_installable_full_site(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            branch_sites = {
                "v4.26.0": root / "site-426",
                "v4.30.0": root / "site-430",
            }
            self._write_branch_site(
                branch_sites["v4.26.0"],
                books={"Demo": "old"},
                papers={"OnlyOld": "paper"},
            )
            self._write_branch_site(
                branch_sites["v4.30.0"],
                books={"Demo": "canonical"},
                papers={},
            )
            historical_doc = (
                branch_sites["v4.26.0"]
                / "docs/ReasBook/Books/Demo/Book.html"
            )
            historical_doc.write_text(
                '<a href="/ReasBook/versions/v4.26.0/books/demo/chapter/">'
                "historical chapter</a>",
                encoding="utf-8",
            )
            rich_route = branch_sites["v4.30.0"] / "demo"
            for relative in (
                Path("index.html"),
                Path("chapter") / "index.html",
                Path("chapter") / "section" / "index.html",
            ):
                target = rich_route / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(
                    "<!doctype html><html><body>"
                    + ("rich route " * 2_000)
                    + "</body></html>",
                    encoding="utf-8",
                )
            dependency = (
                branch_sites["v4.30.0"] / "docs" / "ReasBook" / "Mathlib" / "Heavy.html"
            )
            dependency.parent.mkdir(parents=True)
            dependency.write_text("x" * 200_000, encoding="utf-8")
            refreshed_dependency = dependency.with_name("RefreshTarget.html")
            refreshed_dependency.write_text("refresh target", encoding="utf-8")
            project_doc = (
                branch_sites["v4.30.0"]
                / "docs"
                / "ReasBook"
                / "Books"
                / "Demo"
                / "Book.html"
            )
            project_chapter = project_doc.with_name("Chapter.html")
            project_chapter.write_text("p" * 200_000, encoding="utf-8")
            project_orphan = project_doc.with_name("UnlinkedProjectModule.html")
            project_orphan.write_text("project-owned", encoding="utf-8")
            project_doc.write_text(
                '<!doctype html><html><head><meta http-equiv="refresh" '
                'content="0; url=../../Mathlib/RefreshTarget.html"></head>'
                '<body><a href="../../Mathlib/Heavy.html">'
                'Dependency</a><a href="Chapter.html">Chapter</a></body></html>',
                encoding="utf-8",
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(branch_sites[branch.name]),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            store.write_build_report(report)
            ReleaseSiteAssembler(REPO_ROOT, layout).assemble(spec, report)
            store.transition("validated", completed_stage="site")
            shutil.copytree(
                rich_route,
                layout.site / "versions" / "v4.30.0" / "demo",
                dirs_exist_ok=True,
            )
            # Real v4.30 branch sites split a small indexed landing route from
            # a larger legacy fragment containing chapters but no root index.
            # The fragment must remain available for deep links, but cannot be
            # the catalog redirect target on a static host.
            (layout.site / "versions" / "v4.30.0" / "demo" / "index.html").unlink()
            (layout.site / ".nojekyll").write_text("", encoding="utf-8")
            (layout.site / "private-build-evidence.json").write_text(
                '{"internal":true}\n',
                encoding="utf-8",
            )
            sidebar_only = layout.site / "versions/v4.26.0/books/demo/sidebar-only/index.html"
            sidebar_only.parent.mkdir(parents=True)
            sidebar_only.write_text("<html><body>Old body not retained</body></html>")
            full_site_identity = site_tree_digest(layout.site)

            broken_full = root / "broken-full"
            shutil.copytree(layout.site, broken_full)
            (
                broken_full
                / "versions"
                / "v4.30.0"
                / "docs"
                / "ReasBook"
                / "Books"
                / "Demo"
                / "Book.html"
            ).unlink()
            with self.assertRaisesRegex(
                DeployExecutionError,
                "no project-owned API entry",
            ):
                PagesSiteProjector().project(
                    spec,
                    broken_full,
                    root / "broken-pages",
                )

            PagesSiteProjector().project(spec, layout.site, layout.pages_site)
            self.assertEqual(full_site_identity, site_tree_digest(layout.site))
            self.assertTrue((layout.pages_site / ".nojekyll").is_file())
            self.assertFalse(
                (layout.pages_site / "private-build-evidence.json").exists()
            )
            stub = (
                layout.pages_site
                / "versions"
                / "v4.30.0"
                / "docs"
                / "ReasBook"
                / "Mathlib"
                / "Heavy.html"
            )
            self.assertIn(
                'data-reasbook-doc-stub="true"',
                stub.read_text(encoding="utf-8"),
            )
            self.assertLess(stub.stat().st_size, dependency.stat().st_size)
            self.assertIn(
                "External dependency documentation",
                stub.with_name("RefreshTarget.html").read_text(encoding="utf-8"),
            )
            projected_chapter = (
                layout.pages_site
                / "versions"
                / "v4.30.0"
                / "docs"
                / "ReasBook"
                / "Books"
                / "Demo"
                / "Chapter.html"
            )
            self.assertEqual(
                projected_chapter.read_bytes(),
                project_chapter.read_bytes(),
            )
            self.assertEqual(
                projected_chapter.with_name("UnlinkedProjectModule.html").read_bytes(),
                project_orphan.read_bytes(),
            )
            self.assertTrue(
                (
                    layout.pages_site
                    / "versions"
                    / "v4.26.0"
                    / "docs"
                    / "ReasBook"
                    / "Papers"
                    / "OnlyOld"
                    / "Paper.html"
                ).is_file()
            )
            history_redirect = (
                layout.pages_site
                / "versions/v4.26.0/books/demo/chapter/index.html"
            ).read_text(encoding="utf-8")
            self.assertIn(
                'data-reasbook-history-redirect="true"',
                history_redirect,
            )
            self.assertIn(
                'content="0; url=/ReasBook/versions/v4.30.0/books/demo/chapter/"',
                history_redirect,
            )
            self.assertNotIn('data-reasbook-doc-stub="true"', history_redirect)
            sidebar_redirect = (layout.pages_site / sidebar_only.relative_to(layout.site)).read_text()
            self.assertIn('data-reasbook-history-redirect="true"', sidebar_redirect)
            self.assertNotIn("Old body not retained", sidebar_redirect)
            self.assertFalse((layout.pages_site / "books").exists())
            self.assertFalse((layout.pages_site / "papers").exists())
            self.assertFalse(
                (layout.pages_site / "sites" / "demo" / "pages" / "chapter").exists()
            )
            self.assertIn(
                "/ReasBook/versions/v4.30.0/books/demo/",
                (
                    layout.pages_site / "sites" / "demo" / "pages" / "index.html"
                ).read_text(encoding="utf-8"),
            )
            self.assertTrue(
                (
                    layout.pages_site
                    / "versions"
                    / "v4.30.0"
                    / "demo"
                    / "chapter"
                    / "section"
                    / "index.html"
                ).is_file()
            )
            self.assertIn(
                "/ReasBook/versions/v4.30.0/docs/ReasBook/Books/Demo/Book.html",
                (
                    layout.pages_site / "sites" / "demo" / "docs" / "index.html"
                ).read_text(encoding="utf-8"),
            )
            self.assertTrue(
                (layout.site / "books" / "demo" / "chapter" / "index.html").is_file()
            )
            self.assertEqual(
                project_chapter.read_text(encoding="utf-8"),
                "p" * 200_000,
            )
            with self.assertRaisesRegex(
                DeployExecutionError,
                "budget is 1",
            ):
                PagesSiteProjector(max_site_bytes=1).project(
                    spec,
                    layout.site,
                    root / "over-budget-pages",
                )

            bundler = ReleaseBundler(layout, store, generated_at=self.now)
            full = bundler.package(
                spec,
                report,
                policy=profile(root).artifact("full"),
            )
            pages = bundler.package_pages(
                spec,
                report,
                policy=profile(root).artifact("pages"),
            )
            release_set, bundles = create_release_set(
                layout,
                store,
                spec,
                profile(root).artifacts,
                (full, pages),
            )
            pages = next(item for item in bundles if item.artifact == "pages")
            full = next(item for item in bundles if item.artifact == "full")
            package = ReleasePackageResult(full, pages, release_set)
            self.assertEqual(
                release_set.artifact("pages").bundle,
                Path(pages.bundle).name,
            )
            self.assertEqual(
                set(package.public_dict()["artifacts"]),
                {"full", "pages"},
            )
            self.assertEqual(
                BundleVerifier()
                .verify(Path(pages.bundle), expected_sha256=pages.bundle_sha256)
                .artifact,
                "pages",
            )

            deployment = SelfHostedInstaller(root / "server").install(
                Path(full.bundle),
                release_set=layout.release_set,
                expected_sha256=full.bundle_sha256,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                filesystem_health_only=True,
            )
            current = root / "server" / "current"
            self.assertTrue(current.is_symlink())
            self.assertEqual(
                (current / "public" / "ReasBook" / "index.html").read_text(
                    encoding="utf-8"
                ),
                (layout.site / "index.html").read_text(encoding="utf-8"),
            )
            self.assertEqual(deployment.release_id, spec.release_id)

    def test_self_hosted_install_rejects_pages_artifact_as_full(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            layout.pages_site.mkdir(parents=True)
            (layout.pages_site / "index.html").write_text("site", encoding="utf-8")
            (layout.pages_site / "release-spec.json").write_text(
                json.dumps(spec.public_dict()), encoding="utf-8"
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(root / branch.name),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            pages = ReleaseBundler(layout, store, generated_at=self.now).package_pages(
                spec,
                report,
                policy=profile(root).artifact("pages"),
            )
            with self.assertRaisesRegex(DeployExecutionError, "contains pages"):
                SelfHostedInstaller(root / "server").install(
                    Path(pages.bundle),
                    release_set=layout.release_set,
                    expected_sha256=pages.bundle_sha256,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    filesystem_health_only=True,
                )

    def test_bundle_preflight_rejects_unsafe_members_and_size_bombs(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, _release_set, layout = self._self_hosted_package(root)
            archive = Path(full.bundle)

            with self.assertRaisesRegex(DeployExecutionError, "site-byte"):
                BundleVerifier(max_site_bytes=1).inspect(
                    archive,
                    expected_sha256=full.bundle_sha256,
                )

            traversal = root / "traversal.tar.zst"
            self._write_raw_bundle(
                layout.root,
                traversal,
                "--transform=s|^site/index.html$|../escape.html|",
            )
            with self.assertRaisesRegex(DeployExecutionError, "unsafe bundle member"):
                BundleVerifier().inspect(traversal)

            for link_kind in ("symlink", "hardlink"):
                with self.subTest(link_kind=link_kind):
                    package = root / f"package-{link_kind}"
                    shutil.copytree(layout.site, package / "site")
                    shutil.copy2(layout.manifest, package / "release-manifest.json")
                    link = package / "site" / "linked.html"
                    if link_kind == "symlink":
                        link.symlink_to("index.html")
                    else:
                        link.hardlink_to(package / "site" / "index.html")
                    linked = root / f"{link_kind}.tar.zst"
                    self._write_raw_bundle(package, linked)
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "links or special",
                    ):
                        BundleVerifier().inspect(linked)

    def test_pages_packaging_uses_its_archive_member_policy(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            store.initialize(spec)
            layout.pages_site.mkdir(parents=True)
            (layout.pages_site / "index.html").write_text("site", encoding="utf-8")
            (layout.pages_site / "release-spec.json").write_text(
                json.dumps(spec.public_dict()),
                encoding="utf-8",
            )
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(root / branch.name),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            policy = replace(
                profile(root).artifact("pages"),
                max_archive_members=2,
            )
            with self.assertRaisesRegex(
                DeployExecutionError,
                "archive-member safety limit",
            ):
                ReleaseBundler(
                    layout,
                    store,
                    generated_at=self.now,
                ).package_pages(spec, report, policy=policy)

    def test_site_identity_allows_hidden_files_but_rejects_host_exclusions(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp) / "site"
            challenge = site / ".well-known" / "acme-challenge"
            challenge.parent.mkdir(parents=True)
            (site / ".nojekyll").write_text("", encoding="utf-8")
            challenge.write_text("proof", encoding="utf-8")

            digest, count, total = site_tree_digest(site)
            self.assertRegex(digest, r"^sha256:[0-9a-f]{64}$")
            self.assertEqual(count, 2)
            self.assertEqual(total, len("proof"))

            for reserved in (Path(".git/config"), Path("assets/.github/policy")):
                with self.subTest(path=reserved):
                    target = site / reserved
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text("forbidden", encoding="utf-8")
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "host-excluded path",
                    ):
                        site_tree_digest(site)
                    target.unlink()

    def test_bundle_preflight_rejects_host_excluded_site_paths(self) -> None:
        verifier = BundleVerifier()
        metadata = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        for name in (
            "site/.git/config",
            "site/assets/.github/workflows/publish.yml",
        ):
            with self.subTest(name=name), self.assertRaisesRegex(
                DeployExecutionError,
                "host-excluded path",
            ):
                verifier._validate_members((*metadata, _ArchiveMember(name, "-", 1)))

    def test_bundle_verbose_listing_reports_regular_file_sizes(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, _release_set, layout = self._self_hosted_package(root)

            members = BundleVerifier()._list_archive(Path(full.bundle))
            by_name = {member.name: member for member in members}

            self.assertEqual(by_name["site/index.html"].kind, "-")
            self.assertEqual(
                by_name["site/index.html"].size,
                (layout.site / "index.html").stat().st_size,
            )
            self.assertEqual(by_name["site/"].kind, "d")

    def test_bundle_metadata_limits_precede_json_reads(self) -> None:
        members = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        with tempfile.TemporaryDirectory() as temp:
            bundle = Path(temp) / "fixture.tar.zst"
            bundle.write_bytes(b"fixture")
            for oversized_name in (
                "release-manifest.json",
                "site/release-spec.json",
            ):
                with self.subTest(member=oversized_name):
                    oversized = tuple(
                        _ArchiveMember(
                            member.name,
                            member.kind,
                            2 if member.name == oversized_name else member.size,
                        )
                        for member in members
                    )
                    verifier = BundleVerifier(max_manifest_bytes=1)
                    with (
                        patch.object(
                            verifier,
                            "_list_archive",
                            return_value=oversized,
                        ),
                        patch.object(
                            verifier,
                            "_read_archive_json",
                            side_effect=AssertionError("JSON read before preflight"),
                        ) as read_json,
                    ):
                        with self.assertRaisesRegex(
                            DeployExecutionError,
                            "exceeds its safety limit",
                        ):
                            verifier.inspect(bundle)
                    read_json.assert_not_called()

    def test_bundle_preflight_rejects_escaped_and_control_names(self) -> None:
        verifier = BundleVerifier()
        metadata = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        for unsafe_name in (
            "site/back\\slash.html",
            "site/new\nline.html",
            "site/nul\0name.html",
            "site/delete\x7fname.html",
        ):
            with self.subTest(name=repr(unsafe_name)):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unsafe bundle member",
                ):
                    verifier._validate_members(
                        (*metadata, _ArchiveMember(unsafe_name, "-", 1))
                    )

    def test_bundle_preflight_rejects_path_aliases_and_duplicates(self) -> None:
        verifier = BundleVerifier()
        metadata = (
            _ArchiveMember("release-manifest.json", "-", 1),
            _ArchiveMember("site/", "d", 0),
            _ArchiveMember("site/release-spec.json", "-", 1),
        )
        for alias in (
            "site//alias.html",
            "site/./alias.html",
            "site/alias.html/",
        ):
            with self.subTest(alias=alias):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unsafe bundle member",
                ):
                    verifier._validate_members(
                        (*metadata, _ArchiveMember(alias, "-", 1))
                    )

        with self.assertRaisesRegex(
            DeployExecutionError,
            "duplicate archive members",
        ):
            verifier._validate_members(
                (*metadata, _ArchiveMember("site/release-spec.json", "-", 1))
            )

    def test_self_hosted_health_url_is_restricted_to_safe_http_urls(self) -> None:
        for health_url in (
            "file:///srv/reasbook/release-spec.json",
            "http:///missing-host",
            "http://user:secret@example.test/health",
            "https://example.test/health#fragment",
            "http://example.test:invalid/health",
        ):
            with self.subTest(health_url=health_url):
                with self.assertRaisesRegex(DeployConfigError, "health URL"):
                    SelfHostedInstaller._validate_options(
                        "full",
                        1,
                        0.01,
                        health_url=health_url,
                        filesystem_health_only=False,
                    )

        SelfHostedInstaller._validate_options(
            "full",
            1,
            0.01,
            health_url="http://127.0.0.1/ReasBook/release-spec.json",
            filesystem_health_only=False,
        )

    def test_bundle_preflight_rejects_header_totals_that_disagree(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, _full, _release_set, layout = self._self_hosted_package(root)
            package = root / "mismatched-package"
            shutil.copytree(layout.site, package / "site")
            value = json.loads(layout.manifest.read_text(encoding="utf-8"))
            value["total_bytes"] += 1
            (package / "release-manifest.json").write_text(
                json.dumps(value),
                encoding="utf-8",
            )
            archive = root / "mismatched.tar.zst"
            self._write_raw_bundle(package, archive)

            with self.assertRaisesRegex(
                DeployExecutionError,
                "archive sizes do not match",
            ):
                BundleVerifier().inspect(archive)

    def test_self_hosted_release_set_mismatch_leaves_root_untouched(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, release_set, _layout = self._self_hosted_package(root)
            value = json.loads(release_set.read_text(encoding="utf-8"))
            full_record = next(
                item for item in value["artifacts"] if item["name"] == "full"
            )
            full_record["total_bytes"] += 1
            forged = root / "forged-release-set.json"
            forged.write_text(json.dumps(value), encoding="utf-8")
            deployment_root = root / "server"

            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                SelfHostedInstaller(deployment_root).install(
                    Path(full.bundle),
                    release_set=forged,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=full.bundle_sha256,
                    filesystem_health_only=True,
                )
            self.assertFalse(deployment_root.exists())

    def test_self_hosted_install_requires_an_external_bundle_checksum(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, release_set, _layout = self._self_hosted_package(root)

            with self.assertRaises(TypeError):
                SelfHostedInstaller(root / "server").install(
                    Path(full.bundle),
                    release_set=release_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    filesystem_health_only=True,
                )
            self.assertFalse((root / "server").exists())

    def test_bundle_extraction_target_rejects_symlink_components(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _spec, full, _release_set, _layout = self._self_hosted_package(
                root / "package"
            )
            verifier = BundleVerifier()

            direct_external = root / "direct-external"
            direct_external.mkdir()
            direct_sentinel = direct_external / "sentinel.txt"
            direct_sentinel.write_text("preserve direct", encoding="utf-8")
            direct_link = root / "extract-link"
            direct_link.symlink_to(direct_external, target_is_directory=True)

            parent_external = root / "parent-external"
            parent_external.mkdir()
            parent_sentinel = parent_external / "sentinel.txt"
            parent_sentinel.write_text("preserve parent", encoding="utf-8")
            parent_link = root / "parent-link"
            parent_link.symlink_to(parent_external, target_is_directory=True)

            for label, target in (
                ("target", direct_link),
                ("parent", parent_link / "published"),
            ):
                with self.subTest(label=label), self.assertRaisesRegex(
                    DeployConfigError,
                    "symbolic-link component",
                ):
                    verifier.verify(
                        Path(full.bundle),
                        expected_sha256=full.bundle_sha256,
                        extract_to=target,
                    )

            self.assertTrue(direct_link.is_symlink())
            self.assertEqual(
                direct_sentinel.read_text(encoding="utf-8"),
                "preserve direct",
            )
            self.assertTrue(parent_link.is_symlink())
            self.assertEqual(
                parent_sentinel.read_text(encoding="utf-8"),
                "preserve parent",
            )
            self.assertFalse((parent_external / "published").exists())

    def test_self_hosted_external_checksum_rejects_whole_release_replacement(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _trusted_spec, trusted, _trusted_set, _ = self._self_hosted_package(
                root / "trusted",
                content="trusted release",
            )
            _attacker_spec, attacker, attacker_set, _ = self._self_hosted_package(
                root / "replacement",
                generated_at=self.now.replace(minute=1),
                content="self-consistent replacement",
            )
            deployment_root = root / "server"

            # The replacement carries a self-consistent bundle and ReleaseSet
            # under the same deployment policy.  Only the independently
            # authenticated per-release checksum distinguishes its identity.
            with self.assertRaisesRegex(
                DeployExecutionError,
                "bundle checksum mismatch",
            ):
                SelfHostedInstaller(deployment_root).install(
                    Path(attacker.bundle),
                    release_set=attacker_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=trusted.bundle_sha256,
                    filesystem_health_only=True,
                )
            self.assertFalse(deployment_root.exists())

    def test_self_hosted_health_failure_restores_previous_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_release_set, _ = self._self_hosted_package(
                root, content="first"
            )
            second_spec, second_bundle, second_release_set, _ = (
                self._self_hosted_package(
                    root,
                    generated_at=self.now.replace(minute=1),
                    content="second",
                )
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_release_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )
            with patch.object(
                installer,
                "_probe",
                side_effect=DeployExecutionError("unhealthy"),
            ):
                with self.assertRaisesRegex(DeployExecutionError, "unhealthy"):
                    installer.install(
                        Path(second_bundle.bundle),
                        release_set=second_release_set,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            profile(root).artifacts
                        ),
                        expected_sha256=second_bundle.bundle_sha256,
                        health_url="http://127.0.0.1/health",
                    )

            active = (root / "server" / "current").resolve()
            self.assertEqual(
                active,
                root / "server" / "releases" / first_spec.release_id / "full",
            )
            self.assertNotEqual(first_spec.release_id, second_spec.release_id)

    def test_self_hosted_signal_during_install_restores_previous_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_release_set, _ = self._self_hosted_package(
                root, content="first"
            )
            _second_spec, second_bundle, second_release_set, _ = (
                self._self_hosted_package(
                    root,
                    generated_at=self.now.replace(minute=1),
                    content="second",
                )
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_release_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )

            with patch.object(installer, "_probe", side_effect=SystemExit(143)):
                with self.assertRaises(SystemExit) as raised:
                    installer.install(
                        Path(second_bundle.bundle),
                        release_set=second_release_set,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            profile(root).artifacts
                        ),
                        expected_sha256=second_bundle.bundle_sha256,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / first_spec.release_id / "full",
            )

    def test_self_hosted_interrupt_inside_install_switch_restores_previous(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            _second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )
            original_replace = installer._replace_current

            def replace_then_interrupt(target):
                original_replace(target)
                raise SystemExit(143)

            with patch.object(
                installer,
                "_replace_current",
                side_effect=replace_then_interrupt,
            ):
                with self.assertRaises(SystemExit) as raised:
                    installer.install(
                        Path(second_bundle.bundle),
                        release_set=second_set,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            profile(root).artifacts
                        ),
                        expected_sha256=second_bundle.bundle_sha256,
                        filesystem_health_only=True,
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / first_spec.release_id / "full",
            )

    def test_self_hosted_rollback_health_failure_restores_active_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            installer.install(
                Path(first_bundle.bundle),
                release_set=first_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=first_bundle.bundle_sha256,
                filesystem_health_only=True,
            )
            installer.install(
                Path(second_bundle.bundle),
                release_set=second_set,
                expected_artifact_policy_sha256=artifact_policy_digest(
                    profile(root).artifacts
                ),
                expected_sha256=second_bundle.bundle_sha256,
                filesystem_health_only=True,
            )

            with patch.object(
                installer,
                "_probe",
                side_effect=DeployExecutionError("unhealthy rollback"),
            ):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "unhealthy rollback",
                ):
                    installer.rollback(
                        first_spec.release_id,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / second_spec.release_id / "full",
            )

    def test_self_hosted_signal_during_rollback_restores_active_release(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            for bundle, release_set in (
                (first_bundle, first_set),
                (second_bundle, second_set),
            ):
                installer.install(
                    Path(bundle.bundle),
                    release_set=release_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=bundle.bundle_sha256,
                    filesystem_health_only=True,
                )

            with patch.object(installer, "_probe", side_effect=SystemExit(143)):
                with self.assertRaises(SystemExit) as raised:
                    installer.rollback(
                        first_spec.release_id,
                        health_url="http://127.0.0.1/health",
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / second_spec.release_id / "full",
            )

    def test_self_hosted_interrupt_inside_rollback_switch_restores_active(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            first_spec, first_bundle, first_set, _ = self._self_hosted_package(
                root,
                content="first",
            )
            second_spec, second_bundle, second_set, _ = self._self_hosted_package(
                root,
                generated_at=self.now.replace(minute=1),
                content="second",
            )
            installer = SelfHostedInstaller(root / "server")
            for bundle, release_set in (
                (first_bundle, first_set),
                (second_bundle, second_set),
            ):
                installer.install(
                    Path(bundle.bundle),
                    release_set=release_set,
                    expected_artifact_policy_sha256=artifact_policy_digest(
                        profile(root).artifacts
                    ),
                    expected_sha256=bundle.bundle_sha256,
                    filesystem_health_only=True,
                )
            original_replace = installer._replace_current

            def replace_then_interrupt(target):
                original_replace(target)
                raise SystemExit(143)

            with patch.object(
                installer,
                "_replace_current",
                side_effect=replace_then_interrupt,
            ):
                with self.assertRaises(SystemExit) as raised:
                    installer.rollback(
                        first_spec.release_id,
                        filesystem_health_only=True,
                    )

            self.assertEqual(raised.exception.code, 143)
            self.assertEqual(
                (root / "server" / "current").resolve(),
                root / "server" / "releases" / second_spec.release_id / "full",
            )

    @staticmethod
    def _write_branch_site(
        root: Path,
        *,
        books: dict[str, str],
        papers: dict[str, str],
    ) -> None:
        root.mkdir(parents=True)
        (root / "index.html").write_text("branch", encoding="utf-8")
        for kind, projects, leaf in (
            ("books", books, "Book"),
            ("papers", papers, "Paper"),
        ):
            kind_title = "Books" if kind == "books" else "Papers"
            for project, content in projects.items():
                slug = project.lower()
                pages = root / kind / slug
                (pages / "chapter").mkdir(parents=True)
                html_content = f"<!doctype html><html><body>{content}</body></html>"
                (pages / "index.html").write_text(
                    html_content,
                    encoding="utf-8",
                )
                (pages / "chapter" / "index.html").write_text(
                    "<!doctype html><html><body>chapter</body></html>",
                    encoding="utf-8",
                )
                docs = root / "docs" / "ReasBook" / kind_title / project
                docs.mkdir(parents=True)
                (docs / f"{leaf}.html").write_text(
                    html_content,
                    encoding="utf-8",
                )
                theorem_map = root / "theorem-maps" / kind / slug
                theorem_map.mkdir(parents=True)
                (theorem_map / "index.html").write_text(
                    html_content,
                    encoding="utf-8",
                )

    def test_github_publisher_uploads_then_dispatches_pages(self) -> None:
        class FakeRunner:
            def __init__(
                self,
                paths=(),
                *,
                head: str | None = None,
                status: str = "",
                hidden_draft: bool = False,
            ):
                self.commands = []
                self.paths = paths
                self.head = head or "d" * 40
                self.status = status
                self.tag_exists = False
                self.release_created = False
                self.release_uploaded = False
                self.release_published = False
                self.hidden_draft = hidden_draft

            def run(self, command):
                self.commands.append(command)
                if command.argv == ("git", "rev-parse", "HEAD"):
                    return CommandResult(
                        command=command, returncode=0, stdout=self.head + "\n"
                    )
                if command.argv[0] == "git":
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=self.status,
                    )
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    endpoint = next(
                        part for part in command.argv if part.startswith("repos/")
                    )
                    method = (
                        command.argv[command.argv.index("--method") + 1]
                        if "--method" in command.argv
                        else "GET"
                    )
                    if endpoint.endswith("/immutable-releases"):
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"enabled": True, "enforced_by_owner": False}
                            ),
                        )
                    if "/releases/tags/" in endpoint:
                        if self.release_created:
                            if self.hidden_draft and not self.release_published:
                                return CommandResult(
                                    command=command,
                                    returncode=1,
                                    stderr="gh: Not Found (HTTP 404)",
                                )
                            return CommandResult(
                                command=command,
                                returncode=0,
                                stdout=json.dumps(
                                    {
                                        "id": 123,
                                        "tag_name": (
                                            "reasbook-site-20260901T140000Z-"
                                            "aaaaaaaaaaaa"
                                        ),
                                        "draft": not self.release_published,
                                        "immutable": self.release_published,
                                        "assets": (
                                            github_release_assets(self.paths)
                                            if self.release_uploaded
                                            else []
                                        ),
                                    }
                                ),
                            )
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: Not Found (HTTP 404)",
                        )
                    if "/releases?per_page=100&page=" in endpoint:
                        releases = []
                        if (
                            self.release_created
                            and self.hidden_draft
                            and not self.release_published
                        ):
                            releases.append(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-"
                                        "aaaaaaaaaaaa"
                                    ),
                                    "draft": True,
                                    "immutable": False,
                                    "assets": github_release_assets(self.paths),
                                }
                            )
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(releases),
                        )
                    if endpoint.endswith("/releases/123") and method == "GET":
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-"
                                        "aaaaaaaaaaaa"
                                    ),
                                    "draft": not self.release_published,
                                    "immutable": self.release_published,
                                    "assets": (
                                        github_release_assets(self.paths)
                                        if self.release_uploaded
                                        else []
                                    ),
                                }
                            ),
                        )
                    if endpoint.endswith("/releases") and method == "POST":
                        self.release_created = True
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                    ),
                                    "draft": True,
                                    "immutable": False,
                                    "assets": [],
                                }
                            ),
                        )
                    if endpoint.endswith("/releases/123") and method == "PATCH":
                        self.release_published = True
                        return CommandResult(command=command, returncode=0)
                    if "/commits/" in endpoint:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    if endpoint.endswith("/git/refs") and method == "POST":
                        self.tag_exists = True
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"object": {"type": "commit", "sha": "d" * 40}}
                            ),
                        )
                    if "/git/ref/tags/" in endpoint:
                        if not self.tag_exists:
                            return CommandResult(
                                command=command,
                                returncode=1,
                                stderr="gh: Not Found (HTTP 404)",
                            )
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"object": {"type": "commit", "sha": "d" * 40}}
                            ),
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                if command.argv[1:3] == ("release", "upload"):
                    self.release_uploaded = True
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(root, release_id)
            release_set_sha256 = accepted_release_set_sha256(bundle)
            runner = FakeRunner(assets)
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
                expected_registry_commit="d" * 40,
                expected_tooling_revision=("d" * 40 + "+tooling-sha256:" + "e" * 64),
                expected_release_set_sha256=release_set_sha256,
            )
            publication = publisher.publish(bundle)

            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertEqual(
                verbs,
                [
                    ("api", "repos/acme/reasbook/immutable-releases"),
                    (
                        "api",
                        "repos/acme/reasbook/releases/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    (
                        "api",
                        "repos/acme/reasbook/releases?per_page=100&page=1",
                    ),
                    ("repo", "view"),
                    ("api", "repos/acme/reasbook/commits/main"),
                    ("rev-parse", "HEAD"),
                    ("status", "--porcelain=v1"),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("api", "--method"),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("api", "--method"),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("release", "upload"),
                    (
                        "api",
                        "repos/acme/reasbook/releases/123",
                    ),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("api", "repos/acme/reasbook/immutable-releases"),
                    ("api", "--method"),
                    (
                        "api",
                        "repos/acme/reasbook/releases/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    ("workflow", "run"),
                ],
            )
            self.assertEqual(publication.status, "dispatched")
            self.assertNotIn("secret", " ".join(runner.commands[-1].argv))
            self.assertNotIn(
                "--clobber",
                " ".join(part for command in runner.commands for part in command.argv),
            )
            upload_command = next(
                command
                for command in runner.commands
                if command.argv[1:3] == ("release", "upload")
            )
            self.assertEqual(upload_command.timeout, 7200.0)
            immutable_audit = runner.commands[0]
            self.assertEqual(immutable_audit.timeout, 300.0)
            create_command = next(
                command
                for command in runner.commands
                if command.argv[1:4]
                == (
                    "api",
                    "--method",
                    "POST",
                )
                and command.argv[4] == "repos/acme/reasbook/releases"
            )
            self.assertEqual(
                json.loads(create_command.input_text or "{}"),
                {
                    "tag_name": ("reasbook-site-20260901T140000Z-aaaaaaaaaaaa"),
                    "target_commitish": "d" * 40,
                    "name": (
                        "ReasBook static site " "site-20260901T140000Z-aaaaaaaaaaaa"
                    ),
                    "body": (
                        "Immutable Pages artifact and ReleaseSet generated by "
                        "reasbook-deploy."
                    ),
                    "draft": True,
                    "prerelease": False,
                },
            )
            publish_command = next(
                command
                for command in runner.commands
                if command.argv[1:4]
                == (
                    "api",
                    "--method",
                    "PATCH",
                )
            )
            self.assertEqual(
                publish_command.argv[4],
                "repos/acme/reasbook/releases/123",
            )
            self.assertEqual(
                json.loads(publish_command.input_text or "{}"),
                {"draft": False},
            )
            self.assertFalse(
                any(
                    command.argv[1:3]
                    in {
                        ("release", "create"),
                        ("release", "edit"),
                    }
                    for command in runner.commands
                )
            )
            workflow_command = runner.commands[-1].argv
            self.assertEqual(workflow_command.count("-f"), 1)
            self.assertIn("--ref", workflow_command)
            self.assertEqual(
                workflow_command[workflow_command.index("--ref") + 1],
                "main",
            )

            mismatch_runner = FakeRunner()
            with self.assertRaisesRegex(
                DeployExecutionError,
                "registry commit does not match the GitHub default branch",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=mismatch_runner,
                    expected_registry_commit="c" * 40,
                    expected_tooling_revision=(
                        "c" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle)
            mismatch_verbs = [command.argv[1:3] for command in mismatch_runner.commands]
            self.assertNotIn(("release", "create"), mismatch_verbs)
            self.assertNotIn(("release", "upload"), mismatch_verbs)
            self.assertNotIn(("workflow", "run"), mismatch_verbs)

            dry_mismatch_runner = FakeRunner()
            with self.assertRaisesRegex(
                DeployExecutionError,
                "registry commit does not match the GitHub default branch",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=dry_mismatch_runner,
                    expected_registry_commit="c" * 40,
                    expected_tooling_revision=(
                        "c" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)
            dry_mismatch_verbs = [
                command.argv[1:3] for command in dry_mismatch_runner.commands
            ]
            self.assertNotIn(("release", "create"), dry_mismatch_verbs)
            self.assertNotIn(("release", "upload"), dry_mismatch_verbs)
            self.assertNotIn(("workflow", "run"), dry_mismatch_verbs)

            with self.assertRaisesRegex(
                DeployExecutionError,
                "requires the ReleaseSpec registry commit",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=FakeRunner(),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)

            with self.assertRaisesRegex(
                DeployExecutionError,
                "requires a clean tooling revision",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=FakeRunner(),
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=(
                        "d" * 40 + "+dirty:fingerprint+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)

            audit_runner = FakeRunner(assets)
            planned = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=audit_runner,
                expected_registry_commit="d" * 40,
                expected_tooling_revision=("d" * 40 + "+tooling-sha256:" + "e" * 64),
                expected_release_set_sha256=release_set_sha256,
            ).publish(bundle, dry_run=True)
            self.assertEqual(planned.status, "planned")
            self.assertFalse(audit_runner.tag_exists)
            self.assertFalse(audit_runner.release_created)
            self.assertFalse(audit_runner.release_uploaded)
            self.assertFalse(audit_runner.release_published)
            self.assertIn(
                "X-GitHub-Api-Version: 2026-03-10",
                audit_runner.commands[0].argv,
            )
            dry_run_verbs = [command.argv[1:3] for command in audit_runner.commands]
            self.assertEqual(
                dry_run_verbs,
                [
                    ("api", "repos/acme/reasbook/immutable-releases"),
                    (
                        "api",
                        "repos/acme/reasbook/releases/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                    (
                        "api",
                        "repos/acme/reasbook/releases?per_page=100&page=1",
                    ),
                    ("repo", "view"),
                    ("api", "repos/acme/reasbook/commits/main"),
                    ("rev-parse", "HEAD"),
                    ("status", "--porcelain=v1"),
                    (
                        "api",
                        "repos/acme/reasbook/git/ref/tags/"
                        "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
                    ),
                ],
            )
            self.assertFalse(
                any(
                    command.argv[1:3]
                    in {
                        ("release", "upload"),
                        ("workflow", "run"),
                    }
                    or (
                        command.argv[1] == "api"
                        and "--method" in command.argv
                        and command.argv[command.argv.index("--method") + 1] != "GET"
                    )
                    for command in audit_runner.commands
                )
            )

            resumed_runner = FakeRunner(assets, hidden_draft=True)
            resumed_runner.tag_exists = True
            resumed_runner.release_created = True
            resumed_runner.release_uploaded = True
            resumed = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=resumed_runner,
                expected_registry_commit="d" * 40,
                expected_tooling_revision=(
                    "d" * 40 + "+tooling-sha256:" + "e" * 64
                ),
                expected_release_set_sha256=release_set_sha256,
            ).publish(bundle)
            resumed_verbs = [
                command.argv[1:3] for command in resumed_runner.commands
            ]
            self.assertEqual(resumed.status, "dispatched")
            self.assertNotIn(("release", "upload"), resumed_verbs)
            self.assertFalse(
                any(
                    command.argv[1:4] == ("api", "--method", "POST")
                    and command.argv[4] == "repos/acme/reasbook/releases"
                    for command in resumed_runner.commands
                )
            )
            resumed_publish = next(
                command
                for command in resumed_runner.commands
                if command.argv[1:4] == ("api", "--method", "PATCH")
            )
            self.assertEqual(
                resumed_publish.argv[4],
                "repos/acme/reasbook/releases/123",
            )
            self.assertIn(("workflow", "run"), resumed_verbs)

            dirty_runner = FakeRunner(assets, status=" M local-change.py\n")
            with self.assertRaisesRegex(DeployExecutionError, "clean Git"):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=dirty_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=(
                        "d" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)
            self.assertFalse(dirty_runner.tag_exists)
            self.assertFalse(dirty_runner.release_created)

    def test_github_publisher_rejects_wrong_orphan_or_racing_tag(self) -> None:
        class TagRunner:
            def __init__(
                self,
                *,
                paths=(),
                preexisting_target: str | None = None,
                raced_target: str | None = None,
            ):
                self.commands = []
                self.paths = paths
                self.preexisting_target = preexisting_target
                self.raced_target = raced_target
                self.create_attempted = False
                self.release_created = False
                self.release_uploaded = False
                self.release_published = False

            def run(self, command):
                self.commands.append(command)
                if command.argv == ("git", "rev-parse", "HEAD"):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout="d" * 40 + "\n",
                    )
                if command.argv[0] == "git":
                    return CommandResult(command=command, returncode=0, stdout="")
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] != "api":
                    if command.argv[1:3] == ("release", "upload"):
                        self.release_uploaded = True
                    return CommandResult(command=command, returncode=0)
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                method = (
                    command.argv[command.argv.index("--method") + 1]
                    if "--method" in command.argv
                    else "GET"
                )
                if endpoint.endswith("/immutable-releases"):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"enabled": True, "enforced_by_owner": False}
                        ),
                    )
                if "/releases/tags/" in endpoint:
                    if self.release_created:
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                    ),
                                    "draft": not self.release_published,
                                    "immutable": self.release_published,
                                    "assets": (
                                        github_release_assets(self.paths)
                                        if self.release_uploaded
                                        else []
                                    ),
                                }
                            ),
                        )
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Not Found (HTTP 404)",
                    )
                if "/releases?per_page=100&page=" in endpoint:
                    return CommandResult(command=command, returncode=0, stdout="[]")
                if endpoint.endswith("/releases/123") and method == "GET":
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "id": 123,
                                "tag_name": (
                                    "reasbook-site-20260901T140000Z-"
                                    "aaaaaaaaaaaa"
                                ),
                                "draft": not self.release_published,
                                "immutable": self.release_published,
                                "assets": (
                                    github_release_assets(self.paths)
                                    if self.release_uploaded
                                    else []
                                ),
                            }
                        ),
                    )
                if endpoint.endswith("/releases") and method == "POST":
                    self.release_created = True
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "id": 123,
                                "tag_name": (
                                    "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                ),
                                "draft": True,
                                "immutable": False,
                                "assets": [],
                            }
                        ),
                    )
                if endpoint.endswith("/releases/123") and method == "PATCH":
                    self.release_published = True
                    return CommandResult(command=command, returncode=0)
                if "/commits/" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout="d" * 40 + "\n",
                    )
                if endpoint.endswith("/git/refs") and method == "POST":
                    self.create_attempted = True
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Reference already exists (HTTP 422)",
                    )
                if "/git/ref/tags/" in endpoint:
                    target = (
                        self.raced_target
                        if self.create_attempted
                        else self.preexisting_target
                    )
                    if target is None:
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: Not Found (HTTP 404)",
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": target}}
                        ),
                    )
                raise AssertionError(command.argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(Path(temp), release_id)
            tooling = "d" * 40 + "+tooling-sha256:" + "e" * 64
            release_set_sha256 = accepted_release_set_sha256(bundle)

            orphan_runner = TagRunner(preexisting_target="c" * 40)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "pre-existing release tag",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=orphan_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle)
            self.assertFalse(orphan_runner.create_attempted)
            self.assertFalse(
                any(
                    command.argv[1:3]
                    in {
                        ("release", "create"),
                        ("release", "upload"),
                        ("release", "edit"),
                        ("workflow", "run"),
                    }
                    for command in orphan_runner.commands
                )
            )

            dry_orphan_runner = TagRunner(preexisting_target="c" * 40)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "pre-existing release tag",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=dry_orphan_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)
            self.assertFalse(dry_orphan_runner.create_attempted)
            self.assertFalse(
                any(
                    command.argv[1:3]
                    in {
                        ("release", "upload"),
                        ("workflow", "run"),
                    }
                    or (
                        command.argv[1] == "api"
                        and "--method" in command.argv
                        and command.argv[command.argv.index("--method") + 1] != "GET"
                    )
                    for command in dry_orphan_runner.commands
                )
            )

            missing_after_error_runner = TagRunner()
            with self.assertRaisesRegex(
                DeployExecutionError,
                "cannot create immutable release tag.*422",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=missing_after_error_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle)
            self.assertFalse(
                any(
                    command.argv[1:3] == ("release", "create")
                    for command in missing_after_error_runner.commands
                )
            )

            wrong_race_runner = TagRunner(raced_target="c" * 40)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "concurrently created release tag",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=wrong_race_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle)
            self.assertFalse(
                any(
                    command.argv[1:3] == ("release", "create")
                    for command in wrong_race_runner.commands
                )
            )

            matching_race_runner = TagRunner(
                paths=assets,
                raced_target="d" * 40,
            )
            publication = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=matching_race_runner,
                expected_registry_commit="d" * 40,
                expected_tooling_revision=tooling,
                expected_release_set_sha256=release_set_sha256,
            ).publish(bundle)
            self.assertEqual(publication.status, "dispatched")
            create_ref = next(
                command
                for command in matching_race_runner.commands
                if command.argv[1:3] == ("api", "--method")
            )
            self.assertEqual(
                json.loads(create_ref.input_text or "{}"),
                {
                    "ref": ("refs/tags/" "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"),
                    "sha": "d" * 40,
                },
            )

    def test_github_tag_target_dereferences_annotated_tags(self) -> None:
        class AnnotatedTagRunner:
            def run(self, command):
                endpoint = command.argv[2]
                if "/git/ref/tags/" in endpoint:
                    value = {"object": {"type": "tag", "sha": "a" * 40}}
                elif endpoint.endswith("/git/tags/" + "a" * 40):
                    value = {"object": {"type": "commit", "sha": "c" * 40}}
                else:
                    raise AssertionError(command.argv)
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(value),
                )

        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=AnnotatedTagRunner(),
        )
        self.assertEqual(
            publisher._tag_target("reasbook-site-safe"),
            "c" * 40,
        )

    def test_github_publisher_rechecks_tag_after_upload(self) -> None:
        class MovingTagRunner:
            def __init__(self, paths):
                self.commands = []
                self.paths = paths
                self.tag_reads = 0
                self.release_uploaded = False

            def run(self, command):
                self.commands.append(command)
                if command.argv[1] == "api":
                    endpoint = command.argv[2]
                    if endpoint.endswith("/immutable-releases"):
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"enabled": True, "enforced_by_owner": False}
                            ),
                        )
                    if "/releases/tags/" in endpoint:
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                    ),
                                    "draft": True,
                                    "immutable": False,
                                    "assets": (
                                        github_release_assets(self.paths)
                                        if self.release_uploaded
                                        else []
                                    ),
                                }
                            ),
                        )
                    if endpoint.endswith("/releases/123"):
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-"
                                        "aaaaaaaaaaaa"
                                    ),
                                    "draft": True,
                                    "immutable": False,
                                    "assets": (
                                        github_release_assets(self.paths)
                                        if self.release_uploaded
                                        else []
                                    ),
                                }
                            ),
                        )
                    if "/git/ref/tags/" in endpoint:
                        self.tag_reads += 1
                        target = "c" * 40 if self.tag_reads == 1 else "d" * 40
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"object": {"type": "commit", "sha": target}}
                            ),
                        )
                if command.argv[1:3] == ("release", "upload"):
                    self.release_uploaded = True
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(Path(temp), release_id)
            runner = MovingTagRunner(assets)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "release tag before publication",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=runner,
                    expected_registry_commit="c" * 40,
                    expected_tooling_revision=(
                        "c" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=accepted_release_set_sha256(bundle),
                ).publish(bundle)
            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertIn(("release", "upload"), verbs)
            self.assertNotIn(("release", "edit"), verbs)
            self.assertNotIn(("workflow", "run"), verbs)

    def test_github_release_lookup_fails_closed_on_non_404_error(self) -> None:
        class FailedLookupRunner:
            def run(self, command):
                return CommandResult(
                    command=command,
                    returncode=1,
                    stderr="gh: HTTP 403: rate limit exceeded",
                )

        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=FailedLookupRunner(),
        )
        with self.assertRaisesRegex(DeployExecutionError, "release lookup failed.*403"):
            publisher._release_by_tag_including_drafts("reasbook-site-safe")

    def test_github_release_lookup_recovers_exact_draft_hidden_by_tag_api(
        self,
    ) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"
        draft = {
            "id": 383249278,
            "tag_name": tag,
            "draft": True,
            "immutable": False,
            "assets": [],
        }

        class HiddenDraftRunner:
            def __init__(self):
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                endpoint = command.argv[2]
                if "/releases/tags/" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Not Found (HTTP 404)",
                    )
                if "/releases?per_page=100&page=1" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps([draft]),
                    )
                raise AssertionError(command.argv)

        runner = HiddenDraftRunner()
        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=runner,
        )

        self.assertEqual(publisher._release_by_tag_including_drafts(tag), draft)
        self.assertEqual(len(runner.commands), 2)

    def test_github_rest_release_creation_adopts_only_an_observed_race(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class RaceRunner:
            def __init__(self, *, observed: bool):
                self.observed = observed
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:4] == ("api", "--method", "POST"):
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: already_exists (HTTP 422)",
                    )
                if "/releases/tags/" in command.argv[2]:
                    if not self.observed:
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: Not Found (HTTP 404)",
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "id": 456,
                                "tag_name": tag,
                                "draft": True,
                                "immutable": False,
                                "assets": [],
                            }
                        ),
                    )
                if "/releases?per_page=100&page=" in command.argv[2]:
                    values = []
                    if self.observed:
                        values.append(
                            {
                                "id": 456,
                                "tag_name": tag,
                                "draft": True,
                                "immutable": False,
                                "assets": [],
                            }
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(values),
                    )
                raise AssertionError(command.argv)

        observed = RaceRunner(observed=True)
        release, created = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=observed,
        )._create_draft_release(tag, "c" * 40, "site-fixture")
        self.assertFalse(created)
        self.assertEqual(release["id"], 456)
        create = observed.commands[0]
        self.assertEqual(
            json.loads(create.input_text or "{}")["target_commitish"],
            "c" * 40,
        )
        self.assertIn(
            "X-GitHub-Api-Version: 2026-03-10",
            create.argv,
        )

        missing = RaceRunner(observed=False)
        with self.assertRaisesRegex(
            DeployExecutionError,
            "cannot create draft GitHub Release.*422",
        ):
            GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=missing,
            )._create_draft_release(tag, "c" * 40, "site-fixture")

    def test_github_draft_asset_verification_retries_until_complete(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class AssetRunner:
            def __init__(self, releases):
                self.releases = list(releases)
                self.calls = 0

            def run(self, command):
                self.calls += 1
                release = (
                    self.releases.pop(0) if len(self.releases) > 1 else self.releases[0]
                )
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(release),
                )

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            _, paths = github_pages_bundle_fixture(Path(temp), release_id)
            exact_assets = github_release_assets(paths)
            original = {
                "id": 123,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": [],
            }
            partial = {**original, "assets": exact_assets[:2]}
            complete = {**original, "assets": exact_assets}
            runner = AssetRunner([partial, complete])
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            )
            frozen_assets = publisher._snapshot_assets(tuple(paths))

            with patch("reasbook_deploy_sdk.release.github.time.sleep") as sleep:
                verified = publisher._wait_for_complete_draft_assets(
                    tag,
                    original,
                    tuple(paths),
                    frozen_assets,
                )

            self.assertEqual(verified, complete)
            self.assertEqual(runner.calls, 2)
            sleep.assert_called_once_with(1.0)

    def test_github_draft_asset_verification_uses_known_release_id(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class DraftLookupRunner:
            def __init__(self, release):
                self.release = release
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                if "/releases/tags/" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Not Found (HTTP 404)",
                    )
                if endpoint.endswith("/releases/383249278"):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(self.release),
                    )
                raise AssertionError(command.argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            _, paths = github_pages_bundle_fixture(Path(temp), release_id)
            draft = {
                "id": 383249278,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": github_release_assets(paths),
            }
            runner = DraftLookupRunner(draft)
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            )

            verified = publisher._wait_for_complete_draft_assets(
                tag,
                draft,
                tuple(paths),
                publisher._snapshot_assets(tuple(paths)),
            )

            self.assertEqual(verified, draft)
            self.assertEqual(len(runner.commands), 1)
            self.assertTrue(
                any(
                    part.endswith("/releases/383249278")
                    for part in runner.commands[0].argv
                )
            )

    def test_github_draft_asset_verification_fails_closed(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class AssetRunner:
            def __init__(self, release):
                self.release = release
                self.calls = 0

            def run(self, command):
                self.calls += 1
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(self.release),
                )

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            _, paths = github_pages_bundle_fixture(Path(temp), release_id)
            exact_assets = github_release_assets(paths)
            original = {
                "id": 123,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": [],
            }
            frozen_assets = GitHubReleasePublisher._snapshot_assets(tuple(paths))

            partial_runner = AssetRunner({**original, "assets": exact_assets[:3]})
            partial_publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=partial_runner,
            )
            with patch("reasbook_deploy_sdk.release.github.time.sleep") as sleep:
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "assets did not become complete",
                ):
                    partial_publisher._wait_for_complete_draft_assets(
                        tag,
                        original,
                        tuple(paths),
                        frozen_assets,
                    )
            self.assertEqual(partial_runner.calls, 5)
            self.assertEqual(sleep.call_count, 4)

            mismatched_assets = list(exact_assets)
            mismatched_assets[0] = {
                **mismatched_assets[0],
                "digest": "sha256:" + "0" * 64,
            }
            mismatch_runner = AssetRunner({**original, "assets": mismatched_assets})
            with self.assertRaisesRegex(
                DeployExecutionError,
                "refusing to overwrite",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=mismatch_runner,
                )._wait_for_complete_draft_assets(
                    tag,
                    original,
                    tuple(paths),
                    frozen_assets,
                )
            self.assertEqual(mismatch_runner.calls, 1)

            for changed in (
                {**original, "id": 456, "assets": exact_assets},
                {**original, "tag_name": tag + "-other", "assets": exact_assets},
                {**original, "draft": False, "assets": exact_assets},
            ):
                with self.subTest(changed=changed):
                    identity_runner = AssetRunner(changed)
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "identity changed",
                    ):
                        GitHubReleasePublisher(
                            GitHubPublishProfile(repository="acme/reasbook"),
                            runner=identity_runner,
                        )._wait_for_complete_draft_assets(
                            tag,
                            original,
                            tuple(paths),
                            frozen_assets,
                        )
                    self.assertEqual(identity_runner.calls, 1)

    def test_github_draft_recovers_an_interrupted_starter_asset(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class RecoveryRunner:
            def __init__(self, release):
                self.release = release
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                if "--method" in command.argv:
                    method = command.argv[command.argv.index("--method") + 1]
                    if method == "DELETE":
                        self.release = {**self.release, "assets": []}
                        return CommandResult(command=command, returncode=0)
                if endpoint.endswith("/releases/123"):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(self.release),
                    )
                raise AssertionError(command.argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            _, paths = github_pages_bundle_fixture(Path(temp), release_id)
            tag_release = {
                "id": 123,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": [
                    {
                        "id": 987,
                        "name": paths[0].name,
                        "state": "starter",
                        "size": 0,
                        "digest": None,
                    }
                ],
            }
            runner = RecoveryRunner(tag_release)
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
            )
            with patch("reasbook_deploy_sdk.release.github.time.sleep") as sleep:
                refreshed, missing = publisher._recover_incomplete_draft_assets(
                    tag,
                    tag_release,
                    tuple(paths),
                    publisher._snapshot_assets(tuple(paths)),
                )

            self.assertEqual(refreshed["assets"], [])
            self.assertEqual(missing, tuple(paths))
            self.assertEqual(sleep.call_count, 4)
            delete = next(
                command
                for command in runner.commands
                if command.argv[1:4] == ("api", "--method", "DELETE")
            )
            self.assertTrue(
                any(part.endswith("/releases/assets/987") for part in delete.argv)
            )

            frozen = publisher._snapshot_assets(tuple(paths))
            for unsafe in (
                {**tag_release["assets"][0], "size": 1},
                {**tag_release["assets"][0], "name": "unexpected.bin"},
                {**tag_release["assets"][0], "state": "open"},
            ):
                with self.subTest(unsafe=unsafe), self.assertRaisesRegex(
                    DeployExecutionError,
                    "invalid.*asset metadata",
                ):
                    publisher._validate_existing_release(
                        {**tag_release, "assets": [unsafe]},
                        tuple(paths),
                        frozen,
                    )

    def test_github_publisher_dry_run_never_repairs_a_draft_asset(self) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class DraftRunner:
            def __init__(self, release):
                self.release = release
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1] != "api":
                    raise AssertionError(command.argv)
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                if endpoint.endswith("/immutable-releases"):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"enabled": True, "enforced_by_owner": False}
                        ),
                    )
                if "/releases/tags/" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(self.release),
                    )
                if "/git/ref/tags/" in endpoint:
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "d" * 40}}
                        ),
                    )
                raise AssertionError(command.argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, paths = github_pages_bundle_fixture(Path(temp), release_id)
            tag_release = {
                "id": 123,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": [
                    {
                        "id": 987,
                        "name": paths[0].name,
                        "state": "starter",
                        "size": 0,
                        "digest": None,
                    }
                ],
            }
            runner = DraftRunner(tag_release)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "contains incomplete uploads",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=(
                        "d" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=accepted_release_set_sha256(bundle),
                ).publish(bundle, dry_run=True)

            self.assertFalse(
                any(
                    "--method" in command.argv
                    and command.argv[command.argv.index("--method") + 1] != "GET"
                    for command in runner.commands
                ),
                "a publication dry-run must not repair remote draft assets",
            )

    def test_github_upload_fails_if_a_local_asset_changes_after_validation(
        self,
    ) -> None:
        tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"

        class MutatingRunner:
            def __init__(self, path):
                self.path = path
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:3] == ("release", "upload"):
                    self.path.write_bytes(self.path.read_bytes() + b"\n")
                    return CommandResult(command=command, returncode=0)
                raise AssertionError(command.argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, paths = github_pages_bundle_fixture(Path(temp), release_id)
            runner = MutatingRunner(paths[1])
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
                expected_registry_commit="c" * 40,
                expected_tooling_revision=("c" * 40 + "+tooling-sha256:" + "e" * 64),
                expected_release_set_sha256=accepted_release_set_sha256(bundle),
            )
            draft = {
                "id": 123,
                "tag_name": tag,
                "draft": True,
                "immutable": False,
                "assets": [],
            }
            with (
                patch.object(
                    publisher,
                    "_require_immutable_releases_enabled",
                ),
                patch.object(publisher, "_release_by_tag", return_value=draft),
                patch.object(publisher, "_tag_target", return_value="c" * 40),
            ):
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "assets changed after publication validation",
                ):
                    publisher.publish(bundle)

            self.assertEqual(
                [command.argv[1:3] for command in runner.commands],
                [("release", "upload")],
            )

    def test_github_publisher_dry_run_requires_immutable_release_setting(self) -> None:
        class ImmutableSettingRunner:
            def __init__(self, *, enabled: bool = False, status: int | None = None):
                self.enabled = enabled
                self.status = status
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if not (
                    command.argv[1] == "api"
                    and command.argv[2].endswith("/immutable-releases")
                ):
                    raise AssertionError(command.argv)
                self.assert_api_headers(command.argv)
                if self.status is not None:
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr=f"gh: Forbidden (HTTP {self.status})",
                    )
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(
                        {
                            "enabled": self.enabled,
                            "enforced_by_owner": False,
                        }
                    ),
                )

            @staticmethod
            def assert_api_headers(argv):
                headers = [
                    argv[index + 1] for index, item in enumerate(argv) if item == "-H"
                ]
                if "Accept: application/vnd.github+json" not in headers:
                    raise AssertionError(argv)
                if "X-GitHub-Api-Version: 2026-03-10" not in headers:
                    raise AssertionError(argv)

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, _ = github_pages_bundle_fixture(Path(temp), release_id)
            tooling = "d" * 40 + "+tooling-sha256:" + "e" * 64
            release_set_sha256 = accepted_release_set_sha256(bundle)

            disabled = ImmutableSettingRunner()
            with self.assertRaisesRegex(
                DeployExecutionError,
                "immutable releases are disabled",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=disabled,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)
            self.assertEqual(len(disabled.commands), 1)

            forbidden = ImmutableSettingRunner(status=403)
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"Administration \(read\)",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=forbidden,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)

            server_error = ImmutableSettingRunner(status=500)
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"cannot inspect GitHub immutable releases.*500",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=server_error,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=tooling,
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle, dry_run=True)

            write_forbidden = ImmutableSettingRunner(status=403)
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"Administration \(write\)",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=write_forbidden,
                )._enable_immutable_releases()

    def test_github_publisher_waits_for_release_immutability(self) -> None:
        class ReleaseRunner:
            def __init__(self, states):
                self.states = iter(states)
                self.calls = 0

            def run(self, command):
                self.calls += 1
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(
                        {
                            "draft": False,
                            "immutable": next(self.states),
                            "assets": [],
                        }
                    ),
                )

        runner = ReleaseRunner((False, False, True))
        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/reasbook"),
            runner=runner,
        )
        with patch("reasbook_deploy_sdk.release.github.time.sleep") as sleep:
            release = publisher._wait_for_immutable_release("reasbook-site-safe")
        self.assertTrue(release["immutable"])
        self.assertEqual(runner.calls, 3)
        self.assertEqual(sleep.call_count, 2)

        stuck = ReleaseRunner((False,) * 12)
        with patch(
            "reasbook_deploy_sdk.release.github.time.sleep"
        ), self.assertRaisesRegex(
            DeployExecutionError,
            "did not become immutable",
        ):
            GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=stuck,
            )._wait_for_immutable_release("reasbook-site-safe")

    def test_github_new_release_requires_synced_clean_default_branch(self) -> None:
        class CheckoutRunner:
            def __init__(self, *, head: str, status: str = ""):
                self.head = head
                self.status = status

            def run(self, command):
                if command.argv[0] == "git":
                    output = (
                        self.head if command.argv[1] == "rev-parse" else self.status
                    )
                    return CommandResult(command=command, returncode=0, stdout=output)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout="d" * 40 + "\n",
                )

        profile = GitHubPublishProfile(repository="acme/reasbook")
        with self.assertRaisesRegex(DeployExecutionError, "local HEAD"):
            GitHubReleasePublisher(
                profile,
                runner=CheckoutRunner(head="c" * 40 + "\n"),
            )._trusted_target()
        with self.assertRaisesRegex(DeployExecutionError, "clean Git"):
            GitHubReleasePublisher(
                profile,
                runner=CheckoutRunner(
                    head="d" * 40 + "\n",
                    status="?? uncommitted.py\n",
                ),
            )._trusted_target()

    def test_github_pages_configuration_is_idempotent_and_fail_closed(self) -> None:
        class ConfigureRunner:
            def __init__(self):
                self.commands = []
                self.pages = None
                self.environment = None
                self.policies = None
                self.immutable_releases = False
                self.fail_policy_once = False
                self.after_delete_policies = None

            def run(self, command):
                self.commands.append(command)
                if command.argv[0] == "git":
                    output = (
                        "d" * 40 + "\n"
                        if command.argv[1:3] == ("rev-parse", "HEAD")
                        else ""
                    )
                    return CommandResult(command=command, returncode=0, stdout=output)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] != "api":
                    return CommandResult(command=command, returncode=0)
                if "/commits/" in " ".join(command.argv):
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout="d" * 40 + "\n",
                    )
                endpoint = next(
                    part for part in command.argv if part.startswith("repos/")
                )
                method = (
                    command.argv[command.argv.index("--method") + 1]
                    if "--method" in command.argv
                    else "GET"
                )
                if endpoint.endswith("/immutable-releases"):
                    if method == "PUT":
                        self.immutable_releases = True
                        return CommandResult(command=command, returncode=0)
                    value = {
                        "enabled": self.immutable_releases,
                        "enforced_by_owner": False,
                    }
                elif method == "POST" and endpoint.endswith("/pages"):
                    self.pages = {"build_type": "workflow", "cname": None}
                    value = self.pages
                elif method == "PUT" and endpoint.endswith("/github-pages"):
                    self.environment = {
                        "deployment_branch_policy": {
                            "protected_branches": False,
                            "custom_branch_policies": True,
                        }
                    }
                    self.policies = {
                        "total_count": 0,
                        "branch_policies": [],
                    }
                    value = self.environment
                elif method == "POST" and endpoint.endswith(
                    "/deployment-branch-policies"
                ):
                    if self.fail_policy_once:
                        self.fail_policy_once = False
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: transient failure (HTTP 503)",
                        )
                    request = json.loads(command.input_text or "{}")
                    self.policies = {
                        "total_count": 1,
                        "branch_policies": [request],
                    }
                    value = request
                elif method == "DELETE" and "/deployment-branch-policies/" in endpoint:
                    policy_id = int(endpoint.rsplit("/", 1)[1])
                    records = (self.policies or {}).get("branch_policies", [])
                    matches = [
                        record for record in records if record.get("id") == policy_id
                    ]
                    if len(matches) != 1:
                        return CommandResult(
                            command=command,
                            returncode=1,
                            stderr="gh: Not Found (HTTP 404)",
                        )
                    remaining = [
                        record for record in records if record.get("id") != policy_id
                    ]
                    self.policies = (
                        self.after_delete_policies
                        if self.after_delete_policies is not None
                        else {
                            "total_count": len(remaining),
                            "branch_policies": remaining,
                        }
                    )
                    return CommandResult(command=command, returncode=0)
                elif endpoint.endswith("/pages"):
                    value = self.pages
                elif endpoint.split("?", 1)[0].endswith("/deployment-branch-policies"):
                    value = self.policies
                else:
                    value = self.environment
                if value is None:
                    return CommandResult(
                        command=command,
                        returncode=1,
                        stderr="gh: Not Found (HTTP 404)",
                    )
                return CommandResult(
                    command=command,
                    returncode=0,
                    stdout=json.dumps(value),
                )

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            workflow = root / ".github" / "workflows" / "publish_release_pages.yml"
            workflow.parent.mkdir(parents=True)
            workflow.write_text("name: pages\n", encoding="utf-8")
            runner = ConfigureRunner()
            configurator = GitHubPagesConfigurator(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
                repo_root=root,
            )

            planned = configurator.configure(dry_run=True)
            self.assertEqual(planned.status, "planned")
            self.assertEqual(
                planned.actions,
                (
                    "enable-immutable-releases",
                    "create-pages-workflow-source",
                    "create-github-pages-environment",
                    "allow-default-branch-only",
                ),
            )
            self.assertFalse(
                any(
                    "--method" in command.argv
                    and command.argv[command.argv.index("--method") + 1] != "GET"
                    for command in runner.commands
                )
            )

            with patch.object(
                configurator,
                "_wait_for_immutable_releases_enabled",
                wraps=configurator._wait_for_immutable_releases_enabled,
            ) as wait_for_immutable:
                configured = configurator.configure(
                    immutable_convergence_timeout_seconds=420.0,
                    immutable_convergence_poll_seconds=7.5,
                )
            wait_for_immutable.assert_called_once_with(
                timeout_seconds=420.0,
                poll_interval_seconds=7.5,
            )
            self.assertEqual(configured.status, "configured")
            writes = [
                command
                for command in runner.commands
                if "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] != "GET"
            ]
            self.assertEqual(
                [
                    command.argv[command.argv.index("--method") + 1]
                    for command in writes
                ],
                ["PUT", "POST", "PUT", "POST"],
            )
            self.assertEqual(
                json.loads(writes[-1].input_text or "{}"),
                {"name": "main", "type": "branch"},
            )

            before = len(writes)
            ready = configurator.configure()
            self.assertEqual(ready.status, "ready")
            after = sum(
                "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] != "GET"
                for command in runner.commands
            )
            self.assertEqual(after, before)

            interrupted_runner = ConfigureRunner()
            interrupted_runner.fail_policy_once = True
            interrupted = GitHubPagesConfigurator(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=interrupted_runner,
                repo_root=root,
            )
            with self.assertRaisesRegex(
                DeployExecutionError,
                "create default-branch deployment policy",
            ):
                interrupted.configure()
            self.assertIsNotNone(interrupted_runner.environment)
            self.assertEqual(
                interrupted_runner.policies,
                {"total_count": 0, "branch_policies": []},
            )

            repair_plan = interrupted.configure(dry_run=True)
            self.assertEqual(repair_plan.actions, ("allow-default-branch-only",))
            repaired = interrupted.configure()
            self.assertEqual(repaired.status, "configured")
            self.assertEqual(
                interrupted_runner.policies,
                {
                    "total_count": 1,
                    "branch_policies": [{"name": "main", "type": "branch"}],
                },
            )

            runner.policies = {
                "total_count": 2,
                "branch_policies": [
                    {"name": "main", "type": "branch"},
                    {"name": "v4.30.0", "type": "branch"},
                ],
            }
            before = sum(
                "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] != "GET"
                for command in runner.commands
            )
            with self.assertRaisesRegex(DeployExecutionError, "default branch"):
                configurator.configure()
            after = sum(
                "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] != "GET"
                for command in runner.commands
            )
            self.assertEqual(after, before)

            runner.policies = {
                "total_count": 2,
                "branch_policies": [
                    {"id": 101, "name": "main", "type": "branch"},
                    {"id": 202, "name": "v4.30.0", "type": "branch"},
                ],
            }
            before = len(runner.commands)
            cleanup_plan = configurator.configure(
                dry_run=True,
                remove_policy_id=202,
                expected_policy_name="v4.30.0",
                expected_policy_type="branch",
            )
            self.assertEqual(
                cleanup_plan.actions,
                ("remove-deployment-policy:" "id=202,name=v4.30.0,type=branch",),
            )
            self.assertFalse(
                any(
                    "--method" in command.argv
                    and command.argv[command.argv.index("--method") + 1] == "DELETE"
                    for command in runner.commands[before:]
                )
            )

            apply_start = len(runner.commands)
            cleaned = configurator.configure(
                remove_policy_id=202,
                expected_policy_name="v4.30.0",
                expected_policy_type="branch",
            )
            self.assertEqual(cleaned.status, "configured")
            self.assertEqual(
                runner.policies,
                {
                    "total_count": 1,
                    "branch_policies": [{"id": 101, "name": "main", "type": "branch"}],
                },
            )
            apply_commands = runner.commands[apply_start:]
            delete_position = next(
                index
                for index, command in enumerate(apply_commands)
                if "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] == "DELETE"
            )
            policy_reads = [
                index
                for index, command in enumerate(apply_commands)
                if any(
                    part.endswith("/deployment-branch-policies?per_page=100")
                    for part in command.argv
                )
            ]
            self.assertTrue(any(index < delete_position for index in policy_reads))
            self.assertTrue(any(index > delete_position for index in policy_reads))
            deletes = [
                command
                for command in runner.commands
                if "--method" in command.argv
                and command.argv[command.argv.index("--method") + 1] == "DELETE"
            ]
            self.assertEqual(len(deletes), 1)
            self.assertEqual(
                deletes[0].argv,
                (
                    "gh",
                    "api",
                    "--method",
                    "DELETE",
                    "repos/acme/reasbook/environments/github-pages/"
                    "deployment-branch-policies/202",
                ),
            )
            self.assertIsNone(deletes[0].input_text)

            for missing_type_policy in (101, 202):
                with self.subTest(missing_type_policy=missing_type_policy):
                    runner.policies = {
                        "total_count": 2,
                        "branch_policies": [
                            {
                                "id": 101,
                                "name": "main",
                                **(
                                    {}
                                    if missing_type_policy == 101
                                    else {"type": "branch"}
                                ),
                            },
                            {
                                "id": 202,
                                "name": "v4.30.0",
                                **(
                                    {}
                                    if missing_type_policy == 202
                                    else {"type": "branch"}
                                ),
                            },
                        ],
                    }
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "explicit types",
                    ):
                        configurator.configure(
                            dry_run=True,
                            remove_policy_id=202,
                            expected_policy_name="v4.30.0",
                            expected_policy_type="branch",
                        )

            invalid_removals = (
                (999, "v4.30.0", "branch", "exactly one"),
                (202, "v4.31.0", "branch", "does not exactly match"),
                (202, "v4.30.0", "tag", "does not exactly match"),
                (101, "main", "branch", "default-branch"),
            )
            for policy_id, name, policy_type, message in invalid_removals:
                with self.subTest(
                    policy_id=policy_id,
                    name=name,
                    policy_type=policy_type,
                ):
                    runner.policies = {
                        "total_count": 2,
                        "branch_policies": [
                            {"id": 101, "name": "main", "type": "branch"},
                            {
                                "id": 202,
                                "name": "v4.30.0",
                                "type": "branch",
                            },
                        ],
                    }
                    with self.assertRaisesRegex(DeployExecutionError, message):
                        configurator.configure(
                            dry_run=True,
                            remove_policy_id=policy_id,
                            expected_policy_name=name,
                            expected_policy_type=policy_type,
                        )

            runner.policies = {
                "total_count": 2,
                "branch_policies": [
                    {"id": 101, "name": "main", "type": "branch"},
                    {"name": "v4.30.0", "type": "branch"},
                ],
            }
            with self.assertRaisesRegex(
                DeployExecutionError,
                "positive numeric IDs",
            ):
                configurator.configure(
                    dry_run=True,
                    remove_policy_id=202,
                    expected_policy_name="v4.30.0",
                    expected_policy_type="branch",
                )

            runner.policies = {
                "total_count": 3,
                "branch_policies": [
                    {"id": 101, "name": "main", "type": "branch"},
                    {"id": 202, "name": "v4.30.0", "type": "branch"},
                    {"id": 303, "name": "preview", "type": "branch"},
                ],
            }
            with self.assertRaisesRegex(
                DeployExecutionError,
                "leave exactly the default-branch policy",
            ):
                configurator.configure(
                    dry_run=True,
                    remove_policy_id=202,
                    expected_policy_name="v4.30.0",
                    expected_policy_type="branch",
                )

            runner.policies = {
                "total_count": 2,
                "branch_policies": [
                    {"id": 101, "name": "main", "type": "branch"},
                    {"id": 202, "name": "v4.30.0", "type": "branch"},
                ],
            }
            runner.after_delete_policies = {
                "total_count": 2,
                "branch_policies": [
                    {"id": 101, "name": "main", "type": "branch"},
                    {"id": 303, "name": "racing-policy", "type": "branch"},
                ],
            }
            with self.assertRaisesRegex(DeployExecutionError, "default branch"):
                configurator.configure(
                    remove_policy_id=202,
                    expected_policy_name="v4.30.0",
                    expected_policy_type="branch",
                )

    def test_github_pages_immutable_configuration_wait_is_bounded(self) -> None:
        configurator = GitHubPagesConfigurator(
            GitHubPublishProfile(repository="acme/reasbook")
        )
        with (
            patch.object(
                configurator,
                "_immutable_releases_enabled",
                side_effect=(False, False, True),
            ) as enabled,
            patch("reasbook_deploy_sdk.release.github_client.time.sleep") as sleep,
        ):
            configurator._wait_for_immutable_releases_enabled(
                timeout_seconds=10.0,
                poll_interval_seconds=2.0,
            )
        self.assertEqual(enabled.call_count, 3)
        self.assertEqual(sleep.call_count, 2)
        sleep.assert_called_with(2.0)

        with (
            patch.object(
                configurator,
                "_immutable_releases_enabled",
                return_value=False,
            ),
            patch(
                "reasbook_deploy_sdk.release.github_client.time.monotonic",
                side_effect=(0.0, 0.0, 3.0),
            ),
            patch(
                "reasbook_deploy_sdk.release.github_client.time.sleep"
            ) as timed_sleep,
            self.assertRaisesRegex(
                DeployExecutionError,
                "timed out waiting for GitHub immutable releases",
            ),
        ):
            configurator._wait_for_immutable_releases_enabled(
                timeout_seconds=3.0,
                poll_interval_seconds=2.0,
            )
        timed_sleep.assert_called_once_with(2.0)

        invalid_options = (
            (0.0, 1.0, "timeout"),
            (float("inf"), 1.0, "timeout"),
            (10.0, 0.5, "at least 1 second"),
            (2.0, 3.0, "must not exceed"),
            (True, 1.0, "timeout"),
        )
        for timeout, poll, message in invalid_options:
            with (
                self.subTest(timeout=timeout, poll=poll),
                patch.object(
                    configurator,
                    "_default_branch",
                    side_effect=AssertionError("GitHub must not be called"),
                ),
                self.assertRaisesRegex(DeployExecutionError, message),
            ):
                configurator.configure(
                    dry_run=True,
                    immutable_convergence_timeout_seconds=timeout,
                    immutable_convergence_poll_seconds=poll,
                )

    def test_github_pages_policy_removal_requires_all_expected_fields(self) -> None:
        arguments = [
            "--repo-root",
            str(REPO_ROOT),
            "configure-pages",
            "--profile",
            "github-pages",
            "--remove-policy-id",
            "202",
        ]
        with (
            patch.object(
                GitHubPagesConfigurator,
                "_default_branch",
                side_effect=AssertionError("GitHub must not be called"),
            ),
            self.assertRaisesRegex(DeployExecutionError, "requires .* together"),
        ):
            _main(arguments)

    def test_github_publisher_rejects_full_artifact(self) -> None:
        class NoRunner:
            def run(self, _command):
                raise AssertionError("GitHub must not be called for a full artifact")

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle = root / f"{release_id}.site.tar.zst"
            bundle.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle.read_bytes()).hexdigest()
            manifest = root / "release-manifest.json"
            manifest.write_text(
                json.dumps(release_manifest_fixture(release_id)),
                encoding="utf-8",
            )
            checksums = root / "SHA256SUMS"
            checksums.write_text(f"{digest}  {bundle.name}\n", encoding="utf-8")
            with self.assertRaisesRegex(DeployExecutionError, "pages artifact"):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=NoRunner(),
                ).publish(
                    BundleInfo(
                        release_id,
                        str(bundle),
                        str(manifest),
                        str(checksums),
                        "sha256:" + digest,
                    )
                )

    def test_github_pages_assets_are_bound_by_release_set(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle_path = root / f"{release_id}.pages.site.tar.zst"
            bundle_path.write_text("fixture", encoding="utf-8")
            digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
            site_digest = "sha256:" + "b" * 64
            spec_digest = "sha256:" + "a" * 64
            manifest_path = root / "release-manifest.json"
            manifest_path.write_text(
                json.dumps(
                    release_manifest_fixture(
                        release_id,
                        artifact="pages",
                        spec_digest=spec_digest,
                        site_digest=site_digest,
                    )
                ),
                encoding="utf-8",
            )
            checksums_path = root / "SHA256SUMS"
            checksums_path.write_text(
                f"{digest}  {bundle_path.name}\n", encoding="utf-8"
            )
            release_set_path = root / "release-set.json"
            release_set_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "release_id": release_id,
                        "spec_digest": spec_digest,
                        "generated_at": "2026-09-01T14:00:00Z",
                        "artifact_policy_sha256": "sha256:" + "c" * 64,
                        "artifacts": [
                            {
                                "name": "full",
                                "bundle": f"{release_id}.site.tar.zst",
                                "bundle_sha256": "sha256:" + "d" * 64,
                                "site_tree_sha256": "sha256:" + "e" * 64,
                                "file_count": 2,
                                "total_bytes": 8,
                            },
                            {
                                "name": "pages",
                                "bundle": bundle_path.name,
                                "bundle_sha256": "sha256:" + digest,
                                "site_tree_sha256": site_digest,
                                "file_count": 1,
                                "total_bytes": 7,
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            bundle = BundleInfo(
                release_id,
                str(bundle_path),
                str(manifest_path),
                str(checksums_path),
                "sha256:" + digest,
                artifact="pages",
                release_set=str(release_set_path),
            )
            GitHubReleasePublisher._validate_assets(
                bundle,
                (bundle_path, manifest_path, checksums_path, release_set_path),
                expected_base_path="/ReasBook/",
                expected_spec_digest=spec_digest,
                expected_artifact_policy_sha256="sha256:" + "c" * 64,
            )

            with self.assertRaisesRegex(DeployExecutionError, "expected Pages"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                    expected_base_path="/wrong/",
                )
            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                    expected_artifact_policy_sha256="sha256:" + "0" * 64,
                )

            release_set_path.write_text(
                release_set_path.read_text(encoding="utf-8").replace(
                    "sha256:" + digest, "sha256:" + "0" * 64
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(DeployExecutionError, "does not bind"):
                GitHubReleasePublisher._validate_assets(
                    bundle,
                    (bundle_path, manifest_path, checksums_path, release_set_path),
                )

    def test_github_publisher_rejects_external_manifest_byte_drift(self) -> None:
        class NoRunner:
            @staticmethod
            def run(command):
                raise AssertionError(
                    f"GitHub must not be contacted for invalid assets: {command.argv}"
                )

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(Path(temp), release_id)
            value = json.loads(assets[1].read_text(encoding="utf-8"))
            assets[1].write_text(
                json.dumps(value, separators=(",", ":")),
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                "external release manifest differs from the bundled manifest",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=NoRunner(),
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=(
                        "d" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=accepted_release_set_sha256(bundle),
                ).publish(bundle, dry_run=True)

    def test_github_publisher_revalidates_final_immutable_assets(self) -> None:
        class NoRunner:
            def __init__(self):
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                raise AssertionError(
                    f"unexpected GitHub command after final mismatch: {command.argv}"
                )

        with tempfile.TemporaryDirectory() as temp:
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, assets = github_pages_bundle_fixture(Path(temp), release_id)
            tag = "reasbook-site-20260901T140000Z-aaaaaaaaaaaa"
            exact = {
                "id": 123,
                "tag_name": tag,
                "draft": False,
                "immutable": True,
                "assets": github_release_assets(assets),
            }
            changed_assets = github_release_assets(assets)
            changed_assets[0] = {
                **changed_assets[0],
                "digest": "sha256:" + "0" * 64,
            }
            changed = {**exact, "assets": changed_assets}
            runner = NoRunner()
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/reasbook"),
                runner=runner,
                expected_registry_commit="d" * 40,
                expected_tooling_revision=("d" * 40 + "+tooling-sha256:" + "e" * 64),
                expected_release_set_sha256=accepted_release_set_sha256(bundle),
            )

            with (
                patch.object(
                    publisher,
                    "_require_immutable_releases_enabled",
                ),
                patch.object(publisher, "_release_by_tag", return_value=exact),
                patch.object(publisher, "_tag_target", return_value="d" * 40),
                patch.object(
                    publisher,
                    "_wait_for_immutable_release",
                    return_value=changed,
                ),
                self.assertRaisesRegex(
                    DeployExecutionError,
                    "refusing to overwrite immutable assets",
                ),
            ):
                publisher.publish(bundle)

            self.assertEqual(runner.commands, [])

    def test_github_wait_ignores_runs_that_predate_dispatch(self) -> None:
        class WaitRunner:
            def __init__(self, paths):
                self.list_calls = 0
                self.paths = paths
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    if command.argv[2].endswith("/immutable-releases"):
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"enabled": True, "enforced_by_owner": False}
                            ),
                        )
                    if "/actions/workflows/" in command.argv[2]:
                        self.list_calls += 1
                        old = {
                            "id": 10,
                            "display_title": (
                                "Publish reasbook-site-" "20260901T140000Z-aaaaaaaaaaaa"
                            ),
                            "status": "completed",
                            "conclusion": "success",
                        }
                        payload = [old]
                        if self.list_calls > 1:
                            payload.append(
                                {
                                    "id": 11,
                                    "display_title": old["display_title"],
                                    "status": "completed",
                                    "conclusion": "success",
                                }
                            )
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps({"workflow_runs": payload}),
                        )
                    if "/releases/tags/" in command.argv[2]:
                        assets = github_release_assets(self.paths)
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                    ),
                                    "draft": False,
                                    "immutable": True,
                                    "target_commitish": "c" * 40,
                                    "assets": assets,
                                }
                            ),
                        )
                    if "/commits/" in command.argv[2]:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, paths = github_pages_bundle_fixture(root, release_id)
            release_set_sha256 = accepted_release_set_sha256(bundle)
            runner = WaitRunner(paths)
            spec_digest = "sha256:" + "a" * 64
            publisher = GitHubReleasePublisher(
                GitHubPublishProfile(repository="acme/ReasBook"),
                runner=runner,
                expected_base_path="/ReasBook/",
                expected_spec_digest=spec_digest,
                expected_registry_commit="c" * 40,
                expected_tooling_revision=("c" * 40 + "+tooling-sha256:" + "e" * 64),
                expected_release_set_sha256=release_set_sha256,
            )
            pages_url = "https://acme.github.io/ReasBook/release-spec.json"
            with patch.object(
                publisher,
                "_wait_for_public_pages",
                return_value=pages_url,
            ) as health:
                publication = publisher.publish(
                    bundle,
                    wait=True,
                    wait_timeout_seconds=1,
                )
            self.assertEqual(publication.run_id, 11)
            self.assertEqual(publication.pages_release_spec_url, pages_url)
            health.assert_called_once_with(
                release_id,
                expected_spec_digest=spec_digest,
                expected_registry_commit="c" * 40,
                timeout=300.0,
            )
            self.assertEqual(
                publication.tag,
                "reasbook-site-20260901T140000Z-aaaaaaaaaaaa",
            )
            workflow = next(
                command
                for command in runner.commands
                if command.argv[1:3] == ("workflow", "run")
            )
            self.assertEqual(workflow.argv[workflow.argv.index("--ref") + 1], "main")
            verbs = [command.argv[1:3] for command in runner.commands]
            self.assertIn(("repo", "view"), verbs)
            self.assertNotIn(
                ("release", "edit"),
                verbs,
                "re-dispatch must not mutate an already-published release",
            )
            self.assertFalse(
                any(
                    command.argv[1:4] == ("api", "--method", "PATCH")
                    for command in runner.commands
                ),
                "re-dispatch must not require or republish a draft release",
            )
            self.assertNotIn(("run", "list"), verbs)
            self.assertTrue(
                any(
                    command.argv[1] == "api"
                    and "/actions/workflows/" in command.argv[2]
                    for command in runner.commands
                )
            )
            self.assertFalse(
                any(
                    command.argv[1] == "api" and "/commits/" in command.argv[2]
                    for command in runner.commands
                ),
                "rollback of an old tag must not depend on the current default branch",
            )

            mismatch_runner = WaitRunner(paths)
            with self.assertRaisesRegex(
                DeployExecutionError,
                "registry commit does not match the immutable release tag",
            ):
                GitHubReleasePublisher(
                    GitHubPublishProfile(repository="acme/reasbook"),
                    runner=mismatch_runner,
                    expected_registry_commit="d" * 40,
                    expected_tooling_revision=(
                        "d" * 40 + "+tooling-sha256:" + "e" * 64
                    ),
                    expected_release_set_sha256=release_set_sha256,
                ).publish(bundle)
            mismatch_verbs = [command.argv[1:3] for command in mismatch_runner.commands]
            self.assertNotIn(("release", "edit"), mismatch_verbs)
            self.assertNotIn(("workflow", "run"), mismatch_verbs)

    def test_github_pages_health_probe_binds_public_release_identity(self) -> None:
        class FakeResponse:
            status = 200

            def __init__(self, url, payload):
                self.url = url
                self.payload = payload

            def __enter__(self):
                return self

            def __exit__(self, *_args):
                return False

            def geturl(self):
                return self.url

            def read(self, _limit):
                return self.payload

        release_id = "site-20260901T140000Z-" + "a" * 12
        spec_digest = "sha256:" + "a" * 64
        registry_commit = "c" * 40
        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/ReasBook"),
            expected_base_path="/ReasBook/",
            expected_spec_digest=spec_digest,
            expected_registry_commit=registry_commit,
        )
        url = "https://acme.github.io/ReasBook/release-spec.json"
        payload = json.dumps(
            {
                "release_id": release_id,
                "spec_digest": spec_digest,
                "source": {"registry_commit": registry_commit},
            }
        ).encode()

        with patch(
            "reasbook_deploy_sdk.release.github.urlopen",
            return_value=FakeResponse(url, payload),
        ):
            self.assertEqual(
                publisher._wait_for_public_pages(
                    release_id,
                    expected_spec_digest=spec_digest,
                    expected_registry_commit=registry_commit,
                    timeout=1.0,
                ),
                url,
            )

        stale = payload.replace(registry_commit.encode(), ("d" * 40).encode())
        with (
            patch(
                "reasbook_deploy_sdk.release.github.urlopen",
                return_value=FakeResponse(url, stale),
            ),
            self.assertRaisesRegex(
                DeployExecutionError,
                "reports another release",
            ),
        ):
            publisher._probe_public_pages(
                url,
                release_id=release_id,
                spec_digest=spec_digest,
                registry_commit=registry_commit,
                timeout=1.0,
            )

    def test_github_pages_health_timeout_fails_closed(self) -> None:
        publisher = GitHubReleasePublisher(
            GitHubPublishProfile(repository="acme/ReasBook"),
            expected_base_path="/ReasBook/",
            expected_spec_digest="sha256:" + "a" * 64,
            expected_registry_commit="c" * 40,
        )
        with (
            patch.object(
                publisher,
                "_probe_public_pages",
                side_effect=DeployExecutionError("stale CDN response"),
            ),
            patch(
                "reasbook_deploy_sdk.release.github.time.monotonic",
                side_effect=(0.0, 0.0, 0.0, 1.0, 1.0),
            ),
            self.assertRaisesRegex(
                DeployExecutionError,
                "timed out.*stale CDN response",
            ),
        ):
            publisher._wait_for_public_pages(
                "site-20260901T140000Z-" + "a" * 12,
                expected_spec_digest="sha256:" + "a" * 64,
                expected_registry_commit="c" * 40,
                timeout=1.0,
            )

        with self.assertRaisesRegex(
            DeployExecutionError,
            "requires a run and health URL",
        ):
            GitHubPublication(
                "site-20260901T140000Z-" + "a" * 12,
                "acme/ReasBook",
                "reasbook-site-fixture",
                "publish_release_pages.yml",
                "published",
                run_id=42,
            )

    def test_github_publisher_refuses_to_replace_existing_assets(self) -> None:
        class ExistingRunner:
            def __init__(self):
                self.commands = []

            def run(self, command):
                self.commands.append(command)
                if command.argv[1:3] == ("repo", "view"):
                    return CommandResult(command=command, returncode=0, stdout="main\n")
                if command.argv[1] == "api":
                    if command.argv[2].endswith("/immutable-releases"):
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {"enabled": True, "enforced_by_owner": False}
                            ),
                        )
                    if "/releases/tags/" in command.argv[2]:
                        return CommandResult(
                            command=command,
                            returncode=0,
                            stdout=json.dumps(
                                {
                                    "id": 123,
                                    "tag_name": (
                                        "reasbook-site-20260901T140000Z-" "aaaaaaaaaaaa"
                                    ),
                                    "draft": False,
                                    "immutable": True,
                                    "target_commitish": "c" * 40,
                                    "assets": [
                                        {
                                            "id": 999,
                                            "name": "unexpected.site.tar.zst",
                                            "state": "uploaded",
                                            "size": 1,
                                            "digest": "sha256:" + "0" * 64,
                                        }
                                    ],
                                }
                            ),
                        )
                    if "/commits/" in command.argv[2]:
                        return CommandResult(
                            command=command, returncode=0, stdout="d" * 40 + "\n"
                        )
                    return CommandResult(
                        command=command,
                        returncode=0,
                        stdout=json.dumps(
                            {"object": {"type": "commit", "sha": "c" * 40}}
                        ),
                    )
                return CommandResult(command=command, returncode=0)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            release_id = "site-20260901T140000Z-" + "a" * 12
            bundle, _ = github_pages_bundle_fixture(root, release_id)
            for dry_run in (False, True):
                with self.subTest(dry_run=dry_run):
                    runner = ExistingRunner()
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        "refusing to overwrite",
                    ):
                        GitHubReleasePublisher(
                            GitHubPublishProfile(repository="acme/reasbook"),
                            runner=runner,
                            expected_registry_commit="c" * 40,
                            expected_tooling_revision=(
                                "c" * 40 + "+tooling-sha256:" + "e" * 64
                            ),
                            expected_release_set_sha256=(
                                accepted_release_set_sha256(bundle)
                            ),
                        ).publish(bundle, dry_run=dry_run)

                    verbs = [command.argv[1:3] for command in runner.commands]
                    self.assertNotIn(("release", "upload"), verbs)
                    self.assertNotIn(("workflow", "run"), verbs)

    def test_resume_reuses_successful_branch_build_before_assembly(self) -> None:
        class FakeBuilder:
            def __init__(self, report):
                self.report = report
                self.calls = 0

            def build(self, _spec):
                self.calls += 1
                return self.report

        class FailedAssembler:
            def assemble(self, _spec, _report):
                raise RuntimeError("assembly failed")

        class SuccessfulAssembler:
            def __init__(self, site):
                self.site = site

            def assemble(self, _spec, _report):
                self.site.mkdir(parents=True, exist_ok=True)
                return self.site

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec = self._spec(root)
            layout = ReleaseLayout(root / "cache", spec.release_id)
            store = ReleaseStore(layout)
            state = store.initialize(spec)
            report = ReleaseBuildReport.from_branches(
                spec,
                tuple(
                    BranchBuildResult(
                        branch.name,
                        branch.commit,
                        "success",
                        str(root / branch.name),
                        (StageOutcome("fixture", "success"),),
                    )
                    for branch in spec.branches
                ),
            )
            builder = FakeBuilder(report)
            context = ReleaseContext(profile(root), spec, layout, state)
            service = StaticReleaseService(
                root,
                root / "cache",
                tooling_root=REPO_ROOT,
                source=FakeReleaseSource(),
            )
            with self.assertRaisesRegex(RuntimeError, "assembly failed"):
                service.build(
                    context,
                    builder=builder,
                    assembler=FailedAssembler(),
                )
            self.assertIn("build", store.load_state().completed)

            service.build(
                context,
                builder=builder,
                assembler=SuccessfulAssembler(layout.site),
            )
            self.assertEqual(builder.calls, 1)
            self.assertIn("site", store.load_state().completed)


if __name__ == "__main__":
    unittest.main()
