from __future__ import annotations

from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
from threading import Thread
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.request import urlopen

from reasbook_deploy_sdk import DeployConfigError, DeployExecutionError
from reasbook_deploy_sdk.release.acceptance import ReleaseAcceptanceRunner, _Route
from reasbook_deploy_sdk.release.artifacts import (
    artifact_policy_digest,
    create_release_set,
)
from reasbook_deploy_sdk.release.bundle import ReleaseBundler
from reasbook_deploy_sdk.release.cli import _main, build_parser
from reasbook_deploy_sdk.release.github import GitHubPublication
from reasbook_deploy_sdk.release.models import (
    BranchSpec,
    ProjectSpec,
    ReleasePolicy,
    ReleaseSpec,
    default_artifact_policies,
)
from reasbook_deploy_sdk.release.promotion import require_release_acceptance
from reasbook_deploy_sdk.release.results import (
    BranchBuildResult,
    ReleaseBuildReport,
    StageOutcome,
)
from reasbook_deploy_sdk.release.store import ReleaseLayout, ReleaseStore
from reasbook_deploy_sdk.release.service import StaticReleaseService
from reasbook_deploy_sdk.release.tooling import (
    bind_tooling_revision,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
# Acceptance behavior is exercised against synthetic release fixtures below.
# Give those fixtures an explicit tooling identity instead of hashing the test
# checkout at import time: a source archive intentionally excludes the ignored
# SiFlow operations adapter, while production tooling snapshots fail closed if
# any required entry is absent.
TOOLING_DIGEST = "e" * 64


class ReleaseAcceptanceTests(unittest.TestCase):
    def setUp(self) -> None:
        # ReleaseAcceptanceRunner receives its digest provider through the
        # module boundary.  Most tests are about acceptance semantics rather
        # than repository snapshot discovery, so bind them to the complete
        # synthetic package identity created by _package().  The dedicated
        # mismatch test overrides this provider with a different digest.
        digest = patch(
            "reasbook_deploy_sdk.release.acceptance.tooling_source_digest",
            return_value=TOOLING_DIGEST,
        )
        self.addCleanup(digest.stop)
        digest.start()

    def _package(
        self,
        root: Path,
        *,
        base_path: str = "/ReasBook/",
        include_historical_versions: bool = True,
    ):
        at = datetime(2026, 9, 4, 12, 0, tzinfo=timezone.utc)
        branch = BranchSpec(
            "v4.30.0",
            "b" * 40,
            "leanprover/lean4:v4.30.0",
            "sha256:" + "c" * 64,
        )
        old_branch = BranchSpec(
            "v4.26.0",
            "d" * 40,
            "leanprover/lean4:v4.26.0",
            "sha256:" + "e" * 64,
        )
        policy = ReleasePolicy()
        project = ProjectSpec(
            key="books/Demo",
            kind="books",
            project_id="Demo",
            slug="demo",
            branch=branch.name,
            commit=branch.commit,
            source_path="ReasBook/Books/Demo",
            build_target="Demo",
            canonical=True,
            outputs=policy.outputs(),
        )
        old_project = ProjectSpec(
            key=project.key,
            kind=project.kind,
            project_id=project.project_id,
            slug=project.slug,
            branch=old_branch.name,
            commit=old_branch.commit,
            source_path=project.source_path,
            build_target=project.build_target,
            canonical=False,
            outputs=policy.outputs(),
        )
        spec = ReleaseSpec.create(
            repository="https://github.com/acme/reasbook.git",
            registry_commit="a" * 40,
            tooling_revision=bind_tooling_revision("a" * 40, TOOLING_DIGEST),
            base_path=base_path,
            include_historical_versions=include_historical_versions,
            policy=policy,
            branches=(old_branch, branch),
            projects=(old_project, project),
            resolved_at=at,
        )
        layout = ReleaseLayout(root / "cache", spec.release_id)
        store = ReleaseStore(layout)
        store.initialize(spec)

        site = layout.site
        for relative in (
            Path("."),
            Path("docs"),
            Path("versions"),
            Path("sites/demo"),
            Path("sites/demo/docs"),
            Path("sites/demo/pages"),
            Path("theorem-maps/books/demo"),
            Path("versions/v4.30.0"),
            Path("versions/v4.30.0/books/demo"),
            Path("versions/v4.30.0/theorem-maps/books/demo"),
            Path("versions/v4.26.0"),
            Path("versions/v4.26.0/books/demo"),
            Path("versions/v4.26.0/theorem-maps/books/demo"),
        ):
            destination = site / relative / "index.html"
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(
                "<!doctype html><html><head><title>Fixture</title></head>"
                "<body>fixture</body></html>",
                encoding="utf-8",
            )

        def write_verso_tree(
            verso_root: Path,
            public_root: str,
            *,
            legacy_wrapper: bool = False,
        ) -> None:
            # Supported Verso versions use both the legacy role=main wrapper
            # and the newer article wrapper for their readable content.
            content_open, content_close = (
                ('<div class="main" role="main"><div class="wrap">', "</div></div>")
                if legacy_wrapper
                else ("<article>", "</article>")
            )
            verso_root.mkdir(parents=True, exist_ok=True)
            (verso_root / "index.html").write_text(
                f"<!doctype html><html><body>{content_open}<h1>Demo</h1>"
                "<p>Section index:</p><ul><li>"
                f'<a href="{public_root}chapters/chap01/">Chapter 1</a>'
                f"</li></ul>{content_close}</body></html>",
                encoding="utf-8",
            )
            verso_chapter = verso_root / "chapters" / "chap01" / "index.html"
            verso_chapter.parent.mkdir(parents=True, exist_ok=True)
            verso_chapter.write_text(
                "<!doctype html><html><body><main><h1>Chapter 1</h1>"
                "<p>Section index:</p><ul><li>"
                f'<a href="{public_root}chapters/chap01/section01/">Section 1</a>'
                "</li></ul></main></body></html>",
                encoding="utf-8",
            )
            verso_section = (
                verso_root / "chapters" / "chap01" / "section01" / "index.html"
            )
            verso_section.parent.mkdir(parents=True, exist_ok=True)
            verso_section.write_text(
                "<!doctype html><html><head><title>Section 1</title></head>"
                "<body><article><h1>Section 1</h1>"
                "<p>A readable formalized section.</p></article></body></html>",
                encoding="utf-8",
            )

        for version in ("v4.26.0", "v4.30.0"):
            write_verso_tree(
                site / "versions" / version / "books" / "demo",
                f"{base_path}versions/{version}/books/demo/",
                legacy_wrapper=version == "v4.26.0",
            )
            version_docs = (
                site
                / "versions"
                / version
                / "docs"
                / "ReasBook"
                / "Books"
                / "Demo"
                / "Book.html"
            )
            version_docs.parent.mkdir(parents=True, exist_ok=True)
            version_docs.write_text(
                "<!doctype html><html><head><title>Fixture</title></head>"
                "<body>fixture</body></html>",
                encoding="utf-8",
            )
        write_verso_tree(
            site / "books" / "demo",
            f"{base_path}books/demo/",
        )
        (site / "static").mkdir()
        (site / "static/catalog.css").write_text(
            "html,body{max-width:100%;}", encoding="utf-8"
        )
        (site / "release-spec.json").write_text(
            json.dumps(spec.public_dict()), encoding="utf-8"
        )
        shutil.copytree(site, layout.pages_site)
        direct = (
            f"{base_path}versions/{branch.name}/books/demo/"
            if include_historical_versions
            else f"{base_path}books/demo/"
        )
        (layout.pages_site / "sites/demo/pages/index.html").write_text(
            "<!doctype html><html><head>"
            f'<meta http-equiv="refresh" content="0; url={direct}" />'
            "</head><body>"
            f'<p><a href="{direct}">Open Demo</a></p>'
            "</body></html>",
            encoding="utf-8",
        )

        report = ReleaseBuildReport.from_branches(
            spec,
            (
                BranchBuildResult(
                    old_branch.name,
                    old_branch.commit,
                    "success",
                    str(root / "old-branch-site"),
                    (StageOutcome("fixture", "success"),),
                ),
                BranchBuildResult(
                    branch.name,
                    branch.commit,
                    "success",
                    str(root / "branch-site"),
                    (StageOutcome("fixture", "success"),),
                ),
            ),
        )
        policies = default_artifact_policies()
        bundler = ReleaseBundler(layout, store, generated_at=at)
        full = bundler.package(
            spec,
            report,
            policy=next(item for item in policies if item.name == "full"),
        )
        pages = bundler.package_pages(
            spec,
            report,
            policy=next(item for item in policies if item.name == "pages"),
        )
        create_release_set(layout, store, spec, policies, (full, pages))
        return spec, layout, policies

    @staticmethod
    def _write_valid_promotion_evidence(
        spec: ReleaseSpec,
        layout: ReleaseLayout,
        policies,
    ) -> Path:
        store = ReleaseStore(layout)
        release_set = store.load_release_set()
        bundles = {
            "full": store.load_bundle_info(),
            "pages": store.load_pages_bundle_info(),
        }
        artifacts = {}
        metadata_artifacts = {}
        for name, bundle in bundles.items():
            record = release_set.artifact(name)
            artifacts[name] = {
                "bundle": bundle.bundle,
                "bundle_sha256": bundle.bundle_sha256,
                "site_tree_sha256": record.site_tree_sha256,
                "file_count": record.file_count,
                "total_bytes": record.total_bytes,
                "http": {"status": "passed"},
                "browser": {"status": "passed"},
            }
            manifest = Path(bundle.manifest)
            checksums = Path(bundle.checksums)
            metadata_artifacts[name] = {
                "manifest": str(manifest.resolve(strict=False)),
                "manifest_sha256": (
                    "sha256:" + hashlib.sha256(manifest.read_bytes()).hexdigest()
                ),
                "checksums": str(checksums.resolve(strict=False)),
                "checksums_sha256": (
                    "sha256:" + hashlib.sha256(checksums.read_bytes()).hexdigest()
                ),
            }
        value = {
            "status": "success",
            "release_id": spec.release_id,
            "spec_digest": spec.spec_digest,
            "artifact_policy_sha256": artifact_policy_digest(policies),
            "artifacts": artifacts,
            "metadata": {
                "release_set": str(layout.release_set.resolve(strict=False)),
                "release_set_sha256": (
                    "sha256:"
                    + hashlib.sha256(layout.release_set.read_bytes()).hexdigest()
                ),
                "artifacts": metadata_artifacts,
            },
            "self_hosted": {
                "status": "success",
                "release_id": spec.release_id,
                "filesystem_health": "passed",
            },
        }
        path = layout.cache_root / "validation" / spec.release_id / "latest.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    @staticmethod
    def _fake_playwright(
        root: Path,
        *,
        fail_request: bool = False,
        external_mobile: bool = False,
        redirect_url: str | None = None,
    ):
        executable = root / "fake-chromium"
        executable.write_text("fixture", encoding="utf-8")

        class FakePage:
            def __init__(self, *, mobile: bool):
                self.mobile = mobile
                self.handlers = {}
                self.navigations = []
                self.url = "about:blank"

            def on(self, event, callback):
                self.handlers[event] = callback

            def route(self, pattern, callback):
                self.handlers[pattern] = callback

            def goto(self, url, *, wait_until, timeout):
                if wait_until != "networkidle" or timeout != 30_000:
                    raise AssertionError("browser navigation contract changed")
                self.navigations.append(url)
                self.url = (
                    "https://outside.invalid/escaped/"
                    if self.mobile and external_mobile
                    else (redirect_url or url)
                )
                response = SimpleNamespace(status=200, url=self.url)
                self.handlers["response"](response)
                if fail_request:
                    self.handlers["requestfailed"](
                        SimpleNamespace(
                            url=url.rsplit("/", 1)[0] + "/broken.js",
                            failure="net::ERR_FAILED",
                        )
                    )
                return response

            @staticmethod
            def evaluate(_script):
                return {"scrollWidth": 390, "clientWidth": 390}

            @staticmethod
            def title():
                return "Fixture"

            @staticmethod
            def screenshot(*, path, full_page):
                if not full_page:
                    raise AssertionError("expected full-page screenshot")
                Path(path).write_bytes(b"fixture")

        class FakeBrowser:
            def __init__(self):
                self.pages = []
                self.closed = False

            def new_page(self, **_options):
                page = FakePage(mobile=bool(self.pages))
                self.pages.append(page)
                return page

            def close(self):
                self.closed = True

        browser = FakeBrowser()

        class FakePlaywrightContext:
            def __enter__(self):
                return SimpleNamespace(
                    chromium=SimpleNamespace(
                        executable_path=str(executable),
                        launch=lambda **_options: browser,
                    )
                )

            def __exit__(self, *_args):
                return False

        return (
            SimpleNamespace(sync_playwright=lambda: FakePlaywrightContext()),
            browser,
        )

    def test_validate_cli_surface_is_explicit(self) -> None:
        args = build_parser().parse_args(
            ["validate", "site-20260904T120000Z-" + "a" * 12]
        )
        self.assertEqual(args.release_command, "validate")
        self.assertEqual(args.browser_mode, "auto")
        self.assertFalse(args.keep_workdir)

    def test_gate_verifies_both_artifacts_and_self_host_install(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            result = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            ).run(browser_mode="skip")

            self.assertEqual(result["status"], "success")
            self.assertEqual(set(result["artifacts"]), {"full", "pages"})
            self.assertEqual(
                set(result["metadata"]["artifacts"]),
                {"full", "pages"},
            )
            self.assertRegex(
                result["metadata"]["release_set_sha256"],
                r"^sha256:[0-9a-f]{64}$",
            )
            self.assertEqual(result["self_hosted"]["filesystem_health"], "passed")
            self.assertEqual(
                result["artifacts"]["pages"]["routing_mode"],
                "strict",
            )
            self.assertEqual(
                result["artifacts"]["pages"]["http"]["base_path_redirect_status"],
                308,
            )
            self.assertFalse(result["scratch_retained"])
            diagnostics = Path(result["diagnostics_root"])
            self.assertFalse((diagnostics / "scratch").exists())
            self.assertTrue((diagnostics / "result.json").is_file())
            self.assertTrue((diagnostics / "logs/pages-preview.log").is_file())
            self.assertGreater(result["artifacts"]["pages"]["http"]["route_count"], 5)
            self.assertEqual(
                result["artifacts"]["full"]["browser"]["status"], "skipped"
            )

    def test_acceptance_preview_enforces_production_routing(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            with runner._preview_server(
                layout.pages_site,
                root / "strict-preview.log",
            ) as origin:
                with urlopen(
                    origin + "/ReasBook/static/catalog.css",
                    timeout=5,
                ) as response:
                    self.assertEqual(response.status, 200)

                for alias in ("/static/catalog.css", "/docs/index.html"):
                    with self.subTest(alias=alias), self.assertRaises(
                        HTTPError
                    ) as raised:
                        urlopen(origin + alias, timeout=5)
                    self.assertEqual(raised.exception.code, 404)

    def test_release_preview_cli_forces_production_routing(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, _policies = self._package(Path(temp))
            context = SimpleNamespace(spec=spec, layout=layout)

            class FakeService:
                @staticmethod
                def context(_release_id):
                    return context

            with (
                patch(
                    "reasbook_deploy_sdk.release.cli._service",
                    return_value=FakeService(),
                ),
                patch(
                    "reasbook_deploy_sdk.release.cli.os.execve",
                    side_effect=RuntimeError("preview exec intercepted"),
                ) as execute,
                self.assertRaisesRegex(RuntimeError, "exec intercepted"),
            ):
                _main(
                    [
                        "--repo-root",
                        str(REPO_ROOT),
                        "--cache-root",
                        str(layout.cache_root),
                        "preview",
                        spec.release_id,
                        "--public-prefix",
                        "/workspace/proxy/3000",
                    ]
                )

            command = execute.call_args.args[1]
            self.assertEqual(
                command[command.index("--routing-mode") + 1],
                "strict",
            )

    def test_promotion_accepts_current_required_browser_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            evidence = self._write_valid_promotion_evidence(spec, layout, policies)

            accepted = require_release_acceptance(
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            self.assertEqual(accepted["release_id"], spec.release_id)
            self.assertEqual(
                evidence,
                layout.cache_root / "validation" / spec.release_id / "latest.json",
            )

    def test_promotion_rejects_stale_or_tampered_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            path = self._write_valid_promotion_evidence(spec, layout, policies)
            original = json.loads(path.read_text(encoding="utf-8"))

            mutations = (
                ("release", lambda value: value.__setitem__("release_id", "stale")),
                (
                    "policy",
                    lambda value: value.__setitem__(
                        "artifact_policy_sha256", "sha256:" + "0" * 64
                    ),
                ),
                (
                    "bundle",
                    lambda value: value["artifacts"]["pages"].__setitem__(
                        "bundle_sha256", "sha256:" + "0" * 64
                    ),
                ),
                (
                    "tree",
                    lambda value: value["artifacts"]["full"].__setitem__(
                        "file_count",
                        value["artifacts"]["full"]["file_count"] + 1,
                    ),
                ),
            )
            for label, mutate in mutations:
                with self.subTest(label=label):
                    value = json.loads(json.dumps(original))
                    mutate(value)
                    path.write_text(json.dumps(value), encoding="utf-8")
                    with self.assertRaises(DeployExecutionError):
                        require_release_acceptance(
                            layout,
                            spec,
                            expected_artifact_policy_sha256=(
                                artifact_policy_digest(policies)
                            ),
                        )

            path.write_text(json.dumps(original), encoding="utf-8")
            layout.pages_bundle.write_bytes(b"changed after acceptance")
            with self.assertRaisesRegex(
                DeployExecutionError,
                "bundle changed after release acceptance",
            ):
                require_release_acceptance(
                    layout,
                    spec,
                    expected_artifact_policy_sha256=artifact_policy_digest(policies),
                )

    def test_acceptance_rejects_external_manifest_format_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            value = json.loads(layout.pages_manifest.read_text(encoding="utf-8"))
            layout.pages_manifest.write_text(
                json.dumps(value, separators=(",", ":")),
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                "external release manifest differs from its bundle",
            ):
                ReleaseAcceptanceRunner(
                    REPO_ROOT,
                    layout,
                    spec,
                    expected_artifact_policy_sha256=artifact_policy_digest(policies),
                ).run(browser_mode="skip")

    def test_promotion_rejects_metadata_changed_after_acceptance(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            expected_policy = artifact_policy_digest(policies)

            original_manifest = layout.pages_manifest.read_bytes()
            self._write_valid_promotion_evidence(spec, layout, policies)
            layout.pages_manifest.write_bytes(original_manifest + b"\n")
            with self.assertRaisesRegex(
                DeployExecutionError,
                "pages metadata changed",
            ):
                require_release_acceptance(
                    layout,
                    spec,
                    expected_artifact_policy_sha256=expected_policy,
                )

            layout.pages_manifest.write_bytes(original_manifest)
            original_checksums = layout.checksums.read_bytes()
            self._write_valid_promotion_evidence(spec, layout, policies)
            layout.checksums.write_bytes(original_checksums + b"\n")
            with self.assertRaisesRegex(
                DeployExecutionError,
                "full metadata changed",
            ):
                require_release_acceptance(
                    layout,
                    spec,
                    expected_artifact_policy_sha256=expected_policy,
                )

            layout.checksums.write_bytes(original_checksums)
            self._write_valid_promotion_evidence(spec, layout, policies)
            release_set = json.loads(layout.release_set.read_text(encoding="utf-8"))
            full = next(
                item for item in release_set["artifacts"] if item["name"] == "full"
            )
            full["total_bytes"] += 1
            layout.release_set.write_text(json.dumps(release_set), encoding="utf-8")
            with self.assertRaisesRegex(
                DeployExecutionError,
                "ReleaseSet metadata changed",
            ):
                require_release_acceptance(
                    layout,
                    spec,
                    expected_artifact_policy_sha256=expected_policy,
                )

    def test_promotion_rejects_skipped_browser_or_self_host_check(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            path = self._write_valid_promotion_evidence(spec, layout, policies)
            original = json.loads(path.read_text(encoding="utf-8"))

            mutations = (
                lambda value: value["artifacts"]["pages"]["browser"].__setitem__(
                    "status", "skipped"
                ),
                lambda value: value["artifacts"]["full"]["http"].__setitem__(
                    "status", "skipped"
                ),
                lambda value: value["self_hosted"].__setitem__(
                    "filesystem_health", "skipped"
                ),
            )
            for mutate in mutations:
                value = json.loads(json.dumps(original))
                mutate(value)
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaises(DeployExecutionError):
                    require_release_acceptance(
                        layout,
                        spec,
                        expected_artifact_policy_sha256=artifact_policy_digest(
                            policies
                        ),
                    )

    def test_service_publish_dry_run_consumes_acceptance_evidence(self) -> None:
        class FakePublisher:
            def __init__(self):
                self.calls = 0

            def publish(self, bundle, **_options):
                self.calls += 1
                return GitHubPublication(
                    bundle.release_id,
                    "acme/reasbook",
                    "reasbook-site-fixture",
                    "publish_release_pages.yml",
                    "planned",
                )

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            store = ReleaseStore(layout)
            store.transition("packaged", completed_stage="package")
            context = SimpleNamespace(
                layout=layout,
                spec=spec,
                profile=SimpleNamespace(artifacts=policies),
            )
            service = StaticReleaseService(REPO_ROOT, layout.cache_root)
            publisher = FakePublisher()

            with self.assertRaisesRegex(
                DeployExecutionError,
                "acceptance evidence is missing",
            ):
                service.publish(
                    context,
                    publisher=publisher,
                    dry_run=True,
                )
            self.assertEqual(publisher.calls, 0)

            self._write_valid_promotion_evidence(spec, layout, policies)
            publication = service.publish(
                context,
                publisher=publisher,
                dry_run=True,
            )
            self.assertEqual(publication.status, "planned")
            self.assertEqual(publisher.calls, 1)

    def test_one_click_publish_validates_before_promotion(self) -> None:
        events: list[str] = []
        context = SimpleNamespace(spec=SimpleNamespace(release_id="site-fixture"))
        package = SimpleNamespace()
        publication = GitHubPublication(
            "site-fixture",
            "acme/reasbook",
            "reasbook-site-fixture",
            "publish_release_pages.yml",
            "dispatched",
        )
        service = StaticReleaseService(REPO_ROOT, Path("/tmp/reasbook-unused"))

        with (
            patch.object(service, "plan", return_value=context),
            patch.object(
                service,
                "build",
                side_effect=lambda *_args, **_kwargs: events.append("build") or None,
            ),
            patch.object(
                service,
                "package",
                side_effect=lambda *_args, **_kwargs: events.append("package")
                or package,
            ),
            patch.object(
                service,
                "validate",
                side_effect=lambda *_args, **kwargs: events.append(
                    f"validate:{kwargs['browser_mode']}"
                ),
            ),
            patch.object(
                service,
                "publish",
                side_effect=lambda *_args, **_kwargs: events.append("publish")
                or publication,
            ),
            patch.object(service, "context", return_value=context),
        ):
            result = service.deploy(
                Path("profile.yml"),
                only=("papers/Demo",),
                fetch=False,
            )

        self.assertEqual(
            events,
            ["build", "package", "validate:required", "publish"],
        )
        self.assertIs(result.publication, publication)

    def test_one_click_local_all_active_build_requires_explicit_opt_in(self) -> None:
        service = StaticReleaseService(REPO_ROOT, Path("/tmp/reasbook-unused"))
        with (
            patch.object(
                service,
                "plan",
                side_effect=AssertionError("planning must not start"),
            ),
            self.assertRaisesRegex(
                DeployExecutionError,
                "local builder.*--only.*--allow-local-all-active-build",
            ),
        ):
            service.deploy(Path("profile.yml"), fetch=False)

    def test_resume_uses_the_same_promotion_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            events: list[str] = []
            context = SimpleNamespace(
                spec=spec,
                layout=layout,
                profile=SimpleNamespace(artifacts=policies),
            )
            publication = GitHubPublication(
                spec.release_id,
                "acme/reasbook",
                "reasbook-site-fixture",
                "publish_release_pages.yml",
                "dispatched",
            )

            class FakeService:
                @staticmethod
                def context(_release_id):
                    return context

                @staticmethod
                def build(_context, **_options):
                    events.append("build")
                    return None

                @staticmethod
                def package(_context):
                    events.append("package")
                    return None

                @staticmethod
                def promote(_context, **_options):
                    events.append("promote")
                    return publication

            with (
                patch(
                    "reasbook_deploy_sdk.release.cli._service",
                    return_value=FakeService(),
                ),
                patch("reasbook_deploy_sdk.release.cli._print"),
            ):
                status = _main(
                    [
                        "--repo-root",
                        str(REPO_ROOT),
                        "--cache-root",
                        str(layout.cache_root),
                        "resume",
                        spec.release_id,
                    ]
                )

            self.assertEqual(status, 0)
            self.assertEqual(events, ["build", "package", "promote"])

    def test_self_hosted_publish_dry_run_requires_acceptance(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, _policies = self._package(Path(temp))
            store = ReleaseStore(layout)
            store.transition("packaged", completed_stage="package")
            events: list[str] = []
            context = SimpleNamespace(spec=spec, layout=layout)

            class FakeService:
                @staticmethod
                def context(_release_id):
                    return context

                @staticmethod
                def require_acceptance(_context):
                    events.append("acceptance")

            with (
                patch(
                    "reasbook_deploy_sdk.release.cli._service",
                    return_value=FakeService(),
                ),
                patch("reasbook_deploy_sdk.release.cli._print"),
            ):
                status = _main(
                    [
                        "--repo-root",
                        str(REPO_ROOT),
                        "--cache-root",
                        str(layout.cache_root),
                        "publish",
                        spec.release_id,
                        "--target",
                        "self-hosted",
                        "--deploy-root",
                        str(Path(temp) / "server"),
                        "--filesystem-health-only",
                        "--dry-run",
                    ]
                )

            self.assertEqual(status, 0)
            self.assertEqual(events, ["acceptance"])

    def test_self_hosted_publish_installs_only_the_accepted_full_bundle(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            spec, layout, policies = self._package(Path(temp))
            store = ReleaseStore(layout)
            store.transition("packaged", completed_stage="package")
            bundle = store.load_bundle_info()
            context = SimpleNamespace(
                spec=spec,
                layout=layout,
                profile=SimpleNamespace(artifacts=policies),
            )
            installed: list[dict[str, object]] = []

            class FakeService:
                accepted_sha256 = bundle.bundle_sha256

                @staticmethod
                def context(_release_id):
                    return context

                @classmethod
                def require_acceptance(cls, _context):
                    return {
                        "artifacts": {"full": {"bundle_sha256": cls.accepted_sha256}}
                    }

            class FakeInstaller:
                def __init__(self, deployment_root):
                    self.deployment_root = deployment_root

                def install(self, path, **options):
                    installed.append({"path": path, **options})
                    return {"status": "active"}

            arguments = [
                "--repo-root",
                str(REPO_ROOT),
                "--cache-root",
                str(layout.cache_root),
                "publish",
                spec.release_id,
                "--target",
                "self-hosted",
                "--deploy-root",
                str(Path(temp) / "server"),
                "--filesystem-health-only",
            ]
            with (
                patch(
                    "reasbook_deploy_sdk.release.cli._service",
                    return_value=FakeService(),
                ),
                patch(
                    "reasbook_deploy_sdk.release.cli.SelfHostedInstaller",
                    FakeInstaller,
                ),
                patch("reasbook_deploy_sdk.release.cli._print"),
            ):
                self.assertEqual(_main(arguments), 0)
                self.assertEqual(
                    installed[0]["expected_sha256"],
                    bundle.bundle_sha256,
                )

                FakeService.accepted_sha256 = "sha256:" + "0" * 64
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "bundle metadata changed after release acceptance",
                ):
                    _main(arguments)
            self.assertEqual(len(installed), 1)

    def test_gate_supports_a_site_mounted_at_the_origin_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root, base_path="/")
            result = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            ).run(browser_mode="skip")

            self.assertEqual(result["status"], "success")
            self.assertEqual(
                result["artifacts"]["pages"]["http"]["routes"][0],
                "/",
            )

    def test_http_gate_rejects_a_missing_base_path_redirect(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            class Handler(BaseHTTPRequestHandler):
                def do_GET(self):
                    if self.path.endswith("__reasbook_e2e_missing__"):
                        self.send_response(404)
                        self.end_headers()
                        return
                    if self.path.endswith("release-spec.json"):
                        payload = json.dumps(
                            {
                                "release_id": spec.release_id,
                                "spec_digest": spec.spec_digest,
                            }
                        ).encode()
                        content_type = "application/json"
                    else:
                        payload = b"<!doctype html><html><title>Fixture</title></html>"
                        content_type = "text/html"
                    self.send_response(200)
                    self.send_header("Content-Type", content_type)
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)

                def log_message(self, *_args):
                    return

            server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
            thread = Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "did not redirect",
                ):
                    runner._http_smoke(
                        f"http://127.0.0.1:{server.server_port}",
                        (_Route("root", spec.base_path),),
                        SimpleNamespace(
                            release_id=spec.release_id,
                            spec_digest=spec.spec_digest,
                        ),
                    )
            finally:
                server.shutdown()
                server.server_close()
                thread.join(timeout=5)

    def test_failed_gate_retains_scratch_and_failure_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            layout.pages_bundle.write_bytes(b"tampered")
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                "diagnostics retained",
            ):
                runner.run(browser_mode="skip")

            runs = [
                path
                for path in (
                    layout.cache_root / "validation" / spec.release_id
                ).iterdir()
                if path.is_dir()
            ]
            self.assertEqual(len(runs), 1)
            self.assertTrue((runs[0] / "scratch").is_dir())
            failure = json.loads((runs[0] / "result.json").read_text(encoding="utf-8"))
            self.assertEqual(failure["status"], "failed")
            self.assertTrue(failure["scratch_retained"])

    def test_declared_verso_is_required_per_project(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            self.assertFalse(runner.verso_exemptions)
            (layout.site / "sites/demo/pages/index.html").unlink()

            with self.assertRaisesRegex(
                DeployExecutionError,
                "verso route has no regular index",
            ):
                runner._routes(layout.site, artifact="full")

    def test_direct_verso_semantics_rejects_empty_canonical_and_history(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            empty_shell = (
                "<!doctype html><html><body><article><h1>Demo</h1>"
                "<p>No separate reading sections are published for this version.</p>"
                "</article></body></html>"
            )

            canonical = layout.pages_site / "versions/v4.30.0/books/demo/index.html"
            canonical.write_text(empty_shell, encoding="utf-8")
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"explicit empty shell.*books/Demo@v4\.30\.0",
            ):
                runner._routes(layout.pages_site, artifact="pages")

            shutil.copy2(
                layout.site / "versions/v4.30.0/books/demo/index.html",
                canonical,
            )
            history = layout.site / "versions/v4.26.0/books/demo/index.html"
            history.write_text(empty_shell, encoding="utf-8")
            runner._routes(layout.pages_site, artifact="pages")
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"explicit empty shell.*books/Demo@v4\.26\.0",
            ):
                runner._routes(layout.site, artifact="full")

    def test_direct_verso_semantics_accepts_sections_and_single_pages(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            # The package fixture has a genuine chapter/section page in both
            # immutable version trees.  The canonical adapter is deliberately
            # an empty marker here: semantics must come from the version tree,
            # not from this redirect-wrapper location.
            adapter = layout.pages_site / "sites/demo/pages/index.html"
            adapter.write_text(
                adapter.read_text(encoding="utf-8").replace(
                    "<html>",
                    '<html data-reasbook-verso-empty="true">',
                    1,
                ),
                encoding="utf-8",
            )
            runner._routes(layout.site, artifact="full")
            runner._routes(layout.pages_site, artifact="pages")

            for kind, overview in (("books", "book"), ("papers", "paper")):
                project = ProjectSpec(
                    key=f"{kind}/Standalone",
                    kind=kind,
                    project_id="Standalone",
                    slug="standalone",
                    branch="v4.30.0",
                    commit="b" * 40,
                    source_path=f"ReasBook/{kind.title()}/Standalone",
                    build_target="Standalone",
                    canonical=True,
                    outputs=("verso",),
                )
                relative = Path("versions/v4.30.0") / kind / "standalone"
                page = layout.site / relative / "index.html"
                page.parent.mkdir(parents=True, exist_ok=True)
                page.write_text(
                    "<!doctype html>"
                    '<html data-reasbook-verso-standalone="true"><body><article>'
                    f"<h1>Standalone {overview}</h1>"
                    "<p>This work is intentionally published as one readable page.</p>"
                    "</article></body></html>",
                    encoding="utf-8",
                )
                runner._validate_verso_content(layout.site, relative, project)
                page.write_text(
                    page.read_text(encoding="utf-8").replace(
                        ' data-reasbook-verso-standalone="true"',
                        "",
                        1,
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    r"leaf requires explicit standalone marker and readable prose",
                ):
                    runner._validate_verso_content(layout.site, relative, project)

    def test_direct_verso_semantics_fails_closed_without_readable_content(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            direct = layout.pages_site / "versions/v4.30.0/books/demo"
            shutil.rmtree(direct / "chapters")
            (direct / "index.html").write_text(
                "<!doctype html><html><body><article><h1>Demo</h1>"
                "<p>Section index:</p></article></body></html>",
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                r"no readable chapter, section, or standalone content",
            ):
                runner._routes(layout.pages_site, artifact="pages")

    def test_direct_verso_semantics_rejects_empty_child_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            leaf = (
                layout.pages_site
                / "versions/v4.30.0/books/demo/chapters/chap01/section01/index.html"
            )
            leaf.write_text(
                "<!doctype html><html><body></body></html>",
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                r"no readable chapter, section, or standalone content.*section01",
            ):
                runner._routes(layout.pages_site, artifact="pages")

    def test_direct_verso_semantics_scans_full_payload_for_empty_attribute(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            leaf = (
                layout.pages_site
                / "versions/v4.30.0/books/demo/chapters/chap01/section01/index.html"
            )
            attributes = (
                'data-reasbook-verso-empty = " TRUE "',
                "DATA-REASBOOK-VERSO-EMPTY='true'",
                "data-reasbook-verso-empty\n =\n TrUe",
            )

            for attribute in attributes:
                with self.subTest(attribute=attribute):
                    leaf.write_text(
                        "<!doctype html><html><body><article>"
                        "<p>A readable formalized section appears first.</p>"
                        f"<div {attribute}></div>"
                        "</article></body></html>",
                        encoding="utf-8",
                    )
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        r"explicit empty shell.*books/Demo@v4\.30\.0",
                    ):
                        runner._routes(layout.pages_site, artifact="pages")

    def test_direct_verso_semantics_ignores_hidden_readable_elements(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            leaf = (
                layout.site
                / "versions/v4.30.0/books/demo/chapters/chap01/section01/index.html"
            )
            project = spec.canonical_projects()[0]
            relative = Path("versions/v4.30.0/books/demo")
            hidden_bodies = (
                "<div hidden><p>Hidden prose is not published.</p></div>",
                '<div aria-hidden=" TrUe "><p>Hidden prose is not published.</p></div>',
                '<div style="color:red; DISPLAY : none !important; padding:0">'
                "<p>Hidden prose is not published.</p></div>",
                '<div style="visibility : HIDDEN">'
                "<p>Hidden prose is not published.</p></div>",
                # Closing the inner div must not end the outer hidden scope.
                "<div hidden><div></div>"
                "<p>Still hidden after a nested same-name element.</p></div>",
            )

            for body in hidden_bodies:
                with self.subTest(body=body):
                    leaf.write_text(
                        f"<!doctype html><html><body><article>{body}</article>"
                        "</body></html>",
                        encoding="utf-8",
                    )
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        r"no readable chapter, section, or standalone content.*section01",
                    ):
                        runner._validate_verso_content(
                            layout.site,
                            relative,
                            project,
                        )

            leaf.write_text(
                "<!doctype html><html><body><article>"
                "<div hidden><div></div>"
                "<p>This remains hidden under the outer div.</p></div>"
                "<p>This visible formalized section remains readable.</p>"
                "</article></body></html>",
                encoding="utf-8",
            )
            runner._validate_verso_content(layout.site, relative, project)

    def test_direct_verso_semantics_rejects_redirect_cycle(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            project = layout.pages_site / "versions/v4.30.0/books/demo"
            chapter = project / "chapters/chap01/index.html"
            section = project / "chapters/chap01/section01/index.html"
            chapter.write_text(
                '<!doctype html><html><head><meta http-equiv="refresh" '
                'content="0; url=./section01/" /></head><body>'
                '<a href="./section01/">Open section</a></body></html>',
                encoding="utf-8",
            )
            section.write_text(
                '<!doctype html><html><head><meta http-equiv="refresh" '
                'content="0; url=../" /></head><body>'
                '<a href="../">Open chapter</a></body></html>',
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                DeployExecutionError,
                r"redirect cycle",
            ):
                runner._routes(layout.pages_site, artifact="pages")

    def test_direct_verso_semantics_memoizes_shared_content_dag(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            project_root = layout.site / "versions/v4.30.0/books/demo"
            project = spec.canonical_projects()[0]
            (project_root / "index.html").write_text(
                "<!doctype html><html><body><article><p>Chapter index:</p><ul>"
                '<li><a href="./chapters/chap01/">One</a></li>'
                '<li><a href="./chapters/chap02/">Two</a></li>'
                "</ul></article></body></html>",
                encoding="utf-8",
            )
            for chapter in ("chap01", "chap02"):
                page = project_root / "chapters" / chapter / "index.html"
                page.parent.mkdir(parents=True, exist_ok=True)
                page.write_text(
                    "<!doctype html><html><body><main><p>Section index:</p>"
                    '<ul><li><a href="../../shared/">Shared</a></li></ul>'
                    "</main></body></html>",
                    encoding="utf-8",
                )
            shared = project_root / "shared" / "index.html"
            shared.parent.mkdir(parents=True, exist_ok=True)
            shared.write_text(
                "<!doctype html><html><body><article>"
                "<p>A real shared theorem page.</p>"
                '<a href="../missing/">ordinary cross-link</a>'
                "</article></body></html>",
                encoding="utf-8",
            )

            with patch.object(
                runner,
                "_read_verso_page",
                wraps=runner._read_verso_page,
            ) as read_page:
                runner._validate_verso_content(
                    layout.site,
                    Path("versions/v4.30.0/books/demo"),
                    project,
                )

            shared_reads = sum(
                call.args[0] == shared for call in read_page.call_args_list
            )
            self.assertEqual(shared_reads, 1)

    def test_direct_verso_directory_ignores_backlink_but_requires_forward_child(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            project = spec.canonical_projects()[0]
            relative = Path("versions/v4.30.0/books/demo")
            chapter = layout.site / relative / "chapters/chap01/index.html"
            chapter.write_text(
                "<!doctype html><html><body><main><p>Section index:</p><ul>"
                '<li><a href="../../">Book home</a></li>'
                '<li><a href="./section01/">Section 1</a></li>'
                "</ul></main></body></html>",
                encoding="utf-8",
            )
            runner._validate_verso_content(layout.site, relative, project)

            chapter.write_text(
                "<!doctype html><html><body><main><p>Section index:</p><ul>"
                '<li><a href="../../">Book home</a></li>'
                "</ul></main></body></html>",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"no readable chapter, section, or standalone content.*chap01",
            ):
                runner._validate_verso_content(layout.site, relative, project)

    def test_pages_verso_adapter_binds_refresh_and_anchor_to_direct_root(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            adapter = layout.pages_site / "sites/demo/pages/index.html"
            expected = "/ReasBook/versions/v4.30.0/books/demo/"

            def write_adapter(refresh: str | None, anchor: str) -> None:
                meta = (
                    f'<meta http-equiv="refresh" content="{refresh}" />'
                    if refresh is not None
                    else ""
                )
                adapter.write_text(
                    "<!doctype html><html><head>"
                    f'{meta}</head><body><a href="{anchor}">Open</a>'
                    "</body></html>",
                    encoding="utf-8",
                )

            for refresh in (None, f"1; url={expected}"):
                with self.subTest(refresh=refresh):
                    write_adapter(refresh, expected)
                    with self.assertRaisesRegex(
                        DeployExecutionError,
                        r"zero-second meta refresh",
                    ):
                        runner._routes(layout.pages_site, artifact="pages")

            write_adapter("0; url=/ReasBook/versions/v4.30.0/demo/", expected)
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"adapter refresh does not target",
            ):
                runner._routes(layout.pages_site, artifact="pages")

            write_adapter(f"0; url={expected}", "/ReasBook/")
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"adapter has no anchor targeting",
            ):
                runner._routes(layout.pages_site, artifact="pages")

            write_adapter(f"0; url={expected}", expected)
            (layout.pages_site / "versions/v4.30.0/books/demo/index.html").unlink()
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"canonical-verso-target route has no regular index",
            ):
                runner._routes(layout.pages_site, artifact="pages")

    def test_no_history_release_validates_top_level_canonical_target(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(
                root,
                include_historical_versions=False,
            )
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            pages_routes = runner._routes(layout.pages_site, artifact="pages")
            runner._routes(layout.site, artifact="full")
            self.assertIn(
                "/ReasBook/books/demo/",
                {route.path for route in pages_routes},
            )

            adapter = layout.pages_site / "sites/demo/pages/index.html"
            adapter.write_text(
                '<!doctype html><html><head><meta http-equiv="refresh" '
                'content="0; url=/ReasBook/versions/v4.30.0/books/demo/" />'
                '</head><body><a href="/ReasBook/versions/v4.30.0/books/demo/">'
                "Open</a></body></html>",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                DeployExecutionError,
                r"adapter refresh does not target books/demo/",
            ):
                runner._routes(layout.pages_site, artifact="pages")

    def test_route_matrix_keeps_noncanonical_history_full_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )

            full = {
                route.path for route in runner._routes(layout.site, artifact="full")
            }
            pages = {
                route.path
                for route in runner._routes(layout.pages_site, artifact="pages")
            }
            old_project = "/ReasBook/versions/v4.26.0/books/demo/"
            self.assertIn("/ReasBook/versions/v4.26.0/", full)
            self.assertIn("/ReasBook/versions/v4.30.0/", pages)
            self.assertIn(old_project, full)
            self.assertNotIn(old_project, pages)
            self.assertIn(
                "/ReasBook/versions/v4.26.0/docs/ReasBook/Books/Demo/Book.html",
                full,
            )

            old_docs = (
                layout.site / "versions/v4.26.0/docs/ReasBook/Books/Demo/Book.html"
            )
            old_docs.unlink()
            runner._routes(layout.pages_site, artifact="pages")
            with self.assertRaisesRegex(
                DeployExecutionError,
                "version-docs route",
            ):
                runner._routes(layout.site, artifact="full")

    def test_capability_registry_requires_release_bound_tooling(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)

            with patch(
                "reasbook_deploy_sdk.release.acceptance.tooling_source_digest",
                return_value="f" * 64,
            ), self.assertRaisesRegex(
                DeployConfigError,
                "current tooling differs from ReleaseSpec",
            ):
                ReleaseAcceptanceRunner(
                    REPO_ROOT,
                    layout,
                    spec,
                    expected_artifact_policy_sha256=(artifact_policy_digest(policies)),
                )

    def test_browser_modes_distinguish_skip_from_required(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            routes = (_Route("root", spec.base_path),)
            screenshots = root / "screenshots"

            skipped = runner._browser_smoke(
                "http://127.0.0.1:1",
                routes,
                name="pages",
                mode="skip",
                screenshots=screenshots,
            )
            self.assertEqual(skipped["status"], "skipped")

            with patch(
                "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                side_effect=ModuleNotFoundError(
                    "No module named 'playwright'", name="playwright"
                ),
            ):
                automatic = runner._browser_smoke(
                    "http://127.0.0.1:1",
                    routes,
                    name="pages",
                    mode="auto",
                    screenshots=screenshots,
                )
                self.assertEqual(automatic["status"], "skipped")
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "Playwright is not installed",
                ):
                    runner._browser_smoke(
                        "http://127.0.0.1:1",
                        routes,
                        name="pages",
                        mode="required",
                        screenshots=screenshots,
                    )

            class FakePlaywrightContext:
                def __enter__(self):
                    return SimpleNamespace(
                        chromium=SimpleNamespace(
                            executable_path=str(root / "missing-chromium")
                        )
                    )

                def __exit__(self, *_args):
                    return False

            fake_api = SimpleNamespace(sync_playwright=lambda: FakePlaywrightContext())
            with patch(
                "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                return_value=fake_api,
            ):
                automatic = runner._browser_smoke(
                    "http://127.0.0.1:1",
                    routes,
                    name="pages",
                    mode="auto",
                    screenshots=screenshots,
                )
                self.assertEqual(automatic["status"], "skipped")
                self.assertIn("Chromium is not installed", automatic["reason"])
                with self.assertRaisesRegex(
                    DeployExecutionError,
                    "Chromium is not installed",
                ):
                    runner._browser_smoke(
                        "http://127.0.0.1:1",
                        routes,
                        name="pages",
                        mode="required",
                        screenshots=screenshots,
                    )

    def test_browser_checks_each_representative_route_at_both_widths(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            routes = (
                _Route("root", spec.base_path),
                _Route("project", spec.base_path + "sites/demo/"),
                _Route("docs", spec.base_path + "sites/demo/docs/"),
            )
            fake_api, browser = self._fake_playwright(root)

            with patch(
                "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                return_value=fake_api,
            ):
                result = runner._browser_smoke(
                    "http://127.0.0.1:18000",
                    routes,
                    name="pages",
                    mode="required",
                    screenshots=root / "screenshots",
                )

            expected = ["http://127.0.0.1:18000" + route.path for route in routes]
            self.assertEqual(len(browser.pages), 2)
            self.assertEqual(browser.pages[0].navigations, expected)
            self.assertEqual(browser.pages[1].navigations, expected)
            self.assertTrue(browser.closed)
            self.assertEqual(
                result["routes_by_viewport"]["390x844"],
                [route.path for route in routes],
            )

    def test_browser_allows_readme_redirect_only_from_catalog_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT, layout, spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            readme = "https://github.com/optpku/ReasBook#readme"
            for kind in ("root", "versions", "version-branch", "docs-index", "project", "docs", "verso"):
                with self.subTest(kind=kind):
                    fake_api, browser = self._fake_playwright(root, redirect_url=readme)
                    with patch(
                        "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                        return_value=fake_api,
                    ):
                        def run():
                            return runner._browser_smoke(
                                "http://127.0.0.1:18000",
                                (_Route(kind, spec.base_path),),
                                name="pages", mode="required",
                                screenshots=root / "screenshots",
                            )
                        if kind in {"docs", "verso"}:
                            with self.assertRaisesRegex(DeployExecutionError, "escaped"):
                                run()
                        else:
                            self.assertEqual(run()["status"], "passed")
                    self.assertTrue(browser.closed)

    def test_browser_rejects_transport_failure_and_mobile_origin_escape(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            spec, layout, policies = self._package(root)
            runner = ReleaseAcceptanceRunner(
                REPO_ROOT,
                layout,
                spec,
                expected_artifact_policy_sha256=artifact_policy_digest(policies),
            )
            routes = (_Route("root", spec.base_path),)

            fake_api, failed_request_browser = self._fake_playwright(
                root,
                fail_request=True,
            )
            with patch(
                "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                return_value=fake_api,
            ), self.assertRaisesRegex(
                DeployExecutionError,
                "net::ERR_FAILED",
            ):
                runner._browser_smoke(
                    "http://127.0.0.1:18000",
                    routes,
                    name="pages",
                    mode="required",
                    screenshots=root / "request-failure-screenshots",
                )
            self.assertTrue(failed_request_browser.closed)

            fake_api, escaped_browser = self._fake_playwright(
                root,
                external_mobile=True,
            )
            with patch(
                "reasbook_deploy_sdk.release.acceptance.importlib.import_module",
                return_value=fake_api,
            ), self.assertRaisesRegex(
                DeployExecutionError,
                "390x844",
            ):
                runner._browser_smoke(
                    "http://127.0.0.1:18000",
                    routes,
                    name="pages",
                    mode="required",
                    screenshots=root / "origin-escape-screenshots",
                )
            self.assertTrue(escaped_browser.closed)


if __name__ == "__main__":
    unittest.main()
