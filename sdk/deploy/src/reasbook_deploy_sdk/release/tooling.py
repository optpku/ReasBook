"""Deterministic identity for the operational tooling bundled with a release."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
from typing import Callable, Iterable

from ..errors import DeployConfigError, DeployExecutionError


TOOLING_SNAPSHOT_ENTRIES = (
    Path("SiFlow-sdk/bin"),
    Path("SiFlow-sdk/lib"),
    Path("sdk"),
    Path("scripts/build"),
    Path("scripts/pages"),
    Path("ReasBookWeb/scripts"),
    Path("ReasBookWeb/ReasBookSite.lean"),
    Path("ReasBookWeb/ReasBookSite/LiterateModule.lean"),
    Path("ReasBookWeb/static_files/style.css"),
)
TOOLING_DIGEST_SUFFIX = "+tooling-sha256:"
_DIGEST_RE = re.compile(r"^[0-9a-f]{64}$")
_IGNORED_NAMES = {"__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache"}
_GENERATED_SDK_DIRECTORIES = {"build", "dist"}


def snapshot_ignored_name(name: str) -> bool:
    """Match files omitted while copying a release tooling snapshot."""

    return (
        name in _IGNORED_NAMES
        or name.endswith((".pyc", ".pyo"))
        or name.startswith("test_")
    )


def snapshot_ignored_relative(relative: Path) -> bool:
    """Return whether one repository-relative tooling path is generated.

    ``sdk/build`` is a real capability source directory, while
    ``sdk/build/build`` is packaging output.  Matching the complete relative
    path keeps that distinction explicit and lets hashing and copying share the
    exact same policy.
    """

    relative = Path(relative)
    if relative.is_absolute() or ".." in relative.parts:
        raise DeployExecutionError(
            f"tooling snapshot path must be repository-relative: {relative}"
        )
    if any(snapshot_ignored_name(part) for part in relative.parts):
        return True
    parts = relative.parts
    if len(parts) >= 3 and parts[0] == "sdk":
        if parts[2] in _GENERATED_SDK_DIRECTORIES:
            return True
        if any(part.endswith(".egg-info") for part in parts[2:]):
            return True
    return False


def snapshot_ignore_for(
    repo_root: Path,
) -> Callable[[str, list[str]], set[str]]:
    """Build a ``shutil.copytree`` callback for the canonical path filter."""

    root = Path(repo_root).expanduser().resolve()

    def ignore(directory: str, names: list[str]) -> set[str]:
        current = Path(directory).resolve()
        try:
            parent = current.relative_to(root)
        except ValueError as exc:
            raise DeployExecutionError(
                f"tooling snapshot directory escapes repository: {current}"
            ) from exc
        return {
            name
            for name in names
            if snapshot_ignored_relative(parent / name)
        }

    return ignore


def _digest_files(root: Path, files: Iterable[Path]) -> str:
    digest = hashlib.sha256()
    found = False
    for path in sorted(files, key=lambda item: item.relative_to(root).as_posix()):
        if path.is_symlink() or not path.is_file():
            raise DeployExecutionError(f"tooling tree contains a link or special file: {path}")
        found = True
        relative = path.relative_to(root).as_posix()
        executable = bool(path.stat().st_mode & 0o111)
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0x\0" if executable else b"\0-\0")
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        digest.update(b"\0")
    if not found:
        raise DeployExecutionError("tooling tree contains no files")
    return digest.hexdigest()


def tooling_source_digest(repo_root: Path) -> str:
    """Hash exactly the repository paths copied into remote tooling snapshots."""

    raw_root = Path(repo_root).expanduser()
    if raw_root.is_symlink():
        raise DeployExecutionError(f"tooling source root must not be a symlink: {raw_root}")
    root = raw_root.resolve()
    files: list[Path] = []
    for relative in TOOLING_SNAPSHOT_ENTRIES:
        source = root / relative
        if source.is_symlink() or not (source.is_dir() or source.is_file()):
            raise DeployExecutionError(f"tooling snapshot source is invalid: {source}")
        if source.is_file():
            files.append(source)
            continue
        for path in source.rglob("*"):
            relative_path = path.relative_to(root)
            if snapshot_ignored_relative(relative_path):
                continue
            if path.is_symlink():
                raise DeployExecutionError(f"tooling source contains a link: {path}")
            if path.is_file():
                files.append(path)
            elif not path.is_dir():
                raise DeployExecutionError(
                    f"tooling source contains a special file: {path}"
                )
    return _digest_files(root, files)


def tooling_snapshot_digest(snapshot: Path) -> str:
    """Hash a materialized snapshot, excluding only its identity marker."""

    raw_root = Path(snapshot).expanduser()
    if raw_root.is_symlink():
        raise DeployExecutionError(f"tooling snapshot must not be a symlink: {raw_root}")
    root = raw_root.resolve()
    if not root.is_dir():
        raise DeployExecutionError(f"tooling snapshot is not a directory: {root}")
    files = (
        path
        for path in root.rglob("*")
        if path != root / "snapshot.json"
        and "__pycache__" not in path.parts
        and not path.name.endswith((".pyc", ".pyo"))
        and not path.is_dir()
    )
    return _digest_files(root, files)


def bind_tooling_revision(revision: str, digest: str) -> str:
    """Bind a stable source revision label to one exact tooling tree."""

    base = str(revision).strip()
    normalized = str(digest).strip().lower()
    if not base or any(char in base for char in "\x00\r\n"):
        raise DeployConfigError("tooling revision must be a non-empty safe string")
    if TOOLING_DIGEST_SUFFIX in base:
        raise DeployConfigError("tooling revision is already bound to a tree digest")
    if not _DIGEST_RE.fullmatch(normalized):
        raise DeployConfigError("tooling tree digest must be a full SHA-256")
    return f"{base}{TOOLING_DIGEST_SUFFIX}{normalized}"


def tooling_digest_from_revision(revision: str) -> str:
    """Read the mandatory tree digest encoded in a tooling revision."""

    value = str(revision).strip()
    if TOOLING_DIGEST_SUFFIX not in value:
        raise DeployConfigError(
            "tooling revision is not bound to a tooling tree; create a new ReleaseSpec"
        )
    base, digest = value.rsplit(TOOLING_DIGEST_SUFFIX, 1)
    if not base or not _DIGEST_RE.fullmatch(digest):
        raise DeployConfigError("tooling revision has an invalid tree binding")
    return digest


__all__ = [
    "TOOLING_SNAPSHOT_ENTRIES",
    "bind_tooling_revision",
    "snapshot_ignore_for",
    "snapshot_ignored_relative",
    "tooling_digest_from_revision",
    "tooling_snapshot_digest",
    "tooling_source_digest",
]
