"""Published project rosters shared by the catalog and Verso generator.

These credits are project-level only, never a substitute for a Lean file's
Authors header. Tests require parity with both published README catalogs.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from importlib.resources import files
import json
from urllib.parse import unquote, urlsplit


@dataclass(frozen=True)
class ProjectCredit:
    names: tuple[str, ...]
    source: str
    additional: tuple[tuple[str, tuple[str, ...]], ...] = ()


@lru_cache(maxsize=1)
def project_credits() -> dict[str, ProjectCredit]:
    data = json.loads(files(__package__).joinpath("project_contributors.json").read_text(encoding="utf-8"))
    return {
        f"{category}/{project}": ProjectCredit(
            tuple(names), data["source"].split("#")[0] + f"#{category}",
            tuple((role, tuple(people)) for role, people in
                  data["additional_credits"].get(f"{category}/{project}", {}).items()),
        )
        for category in ("books", "papers") for project, names in data[category].items()
    }


def project_credit(key: str) -> ProjectCredit | None:
    return project_credits().get(key)


def project_key_from_url(url: str) -> str | None:
    """Resolve exact catalog slugs, never a fuzzy match against book titles.

    Some legacy catalog callers only carry (label, URL). The slug is stable across
    sites/, projects/, and versioned reading routes. Ambiguity gets no attribution.
    """
    parts = {part.removesuffix(".html") for part in unquote(urlsplit(url).path).casefold().split("/")}
    matches = [key for key in project_credits() if key.split("/", 1)[1].casefold() in parts]
    return matches[0] if len(matches) == 1 else None
