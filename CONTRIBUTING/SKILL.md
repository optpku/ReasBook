---
name: reasbook-contributing
description: Prepare or review a ReasBook book or paper source contribution on the correct versioned Lean branch, with mandatory per-file code-author attribution and matching main README catalog updates. Use when adding or updating a formalization, checking layout and metadata, auditing author headers, validating locally, or preparing its paired source and catalog handoff. Do not use for unrelated main-branch SDK, release, or website changes.
---

# ReasBook Contributing

Help produce a reviewable source contribution without crossing Lean toolchain
boundaries or modifying unrelated projects.

**Publication blocker: every Lean source file published on GitHub must carry
explicit, verified code-author information in its opening header.** A project
README, paper citation, Git history, or successful build does not replace
per-file attribution. Never publish or hand off a contribution as ready while
its Lean files lack this information.

**Required companion update: a version-branch contribution also requires
synchronizing its corresponding entry in the `main` README.** Do not finish
only the source branch and leave the public catalog outdated. Keep the source
change and the catalog change on their respective base branches.

## Establish the contribution contract

Read [`../CONTRIBUTING.md`](../CONTRIBUTING.md) before changing files. Treat it
as the human-facing procedure and this skill as the agent execution contract.

Determine these values from evidence before editing:

- kind: `book` or `paper`;
- exact, case-sensitive project ID;
- exact Lean/mathlib version;
- target `vX.Y.Z` branch and its registry status; and
- whether this is an addition or an update.

Read `config/toolchains.yml` from `main`, then inspect
`ReasBook/lean-toolchain` and `ReasBook/lakefile.lean` on the target branch.
Normally target only an `Active` branch. Stop for maintainer direction if the
version is unregistered or not active; never silently choose a nearby version.

## Work on the version branch

Book and paper source does not belong on `main`. Create a branch from the
current upstream version ref using `book/<slug>-vX.Y.Z` or
`paper/<slug>-vX.Y.Z`.

Use the branch's existing layout rather than assuming all toolchains are the
same:

- books live in `ReasBook/Books/<ProjectId>/` with `Book.lean` as the
  documentation/check root;
- papers live in `ReasBook/Papers/<ProjectId>/` with `Paper.lean` as the root;
- project library registration may be shared, per-project, or explicit-root;
  follow the target `lakefile.lean` pattern; and
- preserve all unrelated source and user changes.

Every project needs an accurate README. Books use `book.yml` where that branch
supports the metadata contract; papers currently do not use `paper.yml`.
Never infer unknown bibliography, coverage, statistics, or placeholder counts.
Use Python 3.11 or newer for repository metadata helpers.

## Verify code authorship before publication

Follow the [mathlib header convention](https://leanprover-community.github.io/contribute/style.html#header-and-imports)
and the attribution section in the contribution guide. Check every new or
updated `.lean` file, including library roots, compatibility modules, generated
facades, and support code—not only theorem files.

- Put `Authors: Name, Name` in the opening ordinary block comment, before
  `module` or imports. Use `Authors` even for one person.
- Name the people responsible for the Lean code, not automatically the authors
  of the textbook or paper. Keep bibliographic authors separate.
- Verify identities against existing source notices, original source repositories,
  contribution records, and maintainer-confirmed attribution. Do not infer a
  human author from a bot commit, GitHub account, or project-wide roster alone.
- Preserve all existing author, copyright, license, and third-party notices.
  Extend a verified author list when appropriate; do not replace it with the
  current uploader, a tool name, or a generic project/team label.
- For legacy files with only project-level records, get maintainer confirmation
  before using that roster, label its scope, and cite the roster's repository,
  branch/commit, README path and section in the header. For example:
  `Project-level attribution: <owner>/<repo>@<ref>:<README path> (<section>)`.
  Consult third-party notices and pinned upstream source before any project-wide
  fallback: imported code keeps its upstream authors; local adaptations may add
  the confirmed local roster with its scope and source stated separately.
  Never fabricate copyright ownership or silently assign every project
  contributor to every file.
- Fix generator templates as well as checked-in generated files. Regeneration
  must retain existing attribution and attribute new code appropriately.
- Run `scripts/config/check_lean_authors.py` from `main` against the contribution
  checkout as described in the guide. Review the actual names as well as the
  mechanical result. If an identity remains uncertain, report the exact files
  and stop publication until the maintainer resolves it.

## Synchronize the corresponding main README entry

For every book or paper addition or update on a version branch, inspect the
matching project entry on current upstream `main` and prepare its companion
catalog update. This is part of the contribution, not an optional later task.

- Use the exact project ID to find the entry in `README.md` and
  `README.zh-CN.md`. Update the corresponding catalog-folder README under
  `ReasBook/Books/<ProjectId>/` or `ReasBook/Papers/<ProjectId>/` when affected.
- Keep the source branch/version links, verified code contributors, coverage
  or proof status, and resource links consistent with the changed project.
  Keep paper authors separate from code authors and preserve other versions
  and curated proof-route entries. Do not advertise pending Docs, Verso, or
  theorem maps as already published.
- Prepare the README/catalog-only change on a separate branch based on `main`;
  keep Lean mathematical source on the exact version branch. Never merge a
  version branch into `main` just to update its README, or switch away from a
  dirty checkout without preserving the user's work.
- Review both language versions and the affected source paths/links. If a
  source-only correction leaves all catalog facts unchanged, explicitly record
  which main entry was checked and why no README edit is needed; do not create
  a meaningless diff or silently skip the synchronization check.
- When PR creation is requested, use the version branch as the source PR base
  and `main` as the companion catalog PR base, and cross-link the two. Otherwise
  hand off both local change sets and their base branches without publishing.

Do not report the contribution complete while a needed main README update is
missing. If the requested scope or permissions prevent the companion change,
report that pending work explicitly and request the necessary direction.

## Validate proportionally

Check the root file directly with the branch-pinned toolchain:

```bash
cd ReasBook
lake exe cache get
lake env lean Books/<ProjectId>/Book.lean
# or: lake env lean Papers/<ProjectId>/Paper.lean
```

The cache command is optional. Use a dedicated `lake build <ProjectId>` only
when the branch defines that library. Do not launch repository-wide or remote
builds unless the user requests them; record any validation not run.

Before handoff, compare against `upstream/vX.Y.Z`, inspect deletions separately,
and ensure generated caches, sites, logs, and compiled artifacts are absent.
Do not claim PR CI ran: workflow coverage varies by version branch.

## Prepare the handoff

Use the kind-specific `[Book]` or `[Paper]` PR title from the contribution
guide. Report the exact base branch, toolchain, changed scope, commands run,
results, placeholder counts, and any validation still pending. Do not commit,
push, or open a PR unless the user asked for that external action.
Include the author-header check result and any unresolved attribution in the
handoff and PR report. Missing or unverified code authorship is a blocker, not
an optional documentation follow-up.
Report main README synchronization separately: affected project entry, files
updated, local change set or companion PR, and any remaining dependency. A
completed source PR alone does not complete the catalog synchronization.
