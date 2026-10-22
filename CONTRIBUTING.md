# Contributing to ReasBook

Thank you for contributing a Lean formalization. This guide covers book and
paper source contributions and their required companion README catalog
updates on `main`. Unrelated catalog maintenance, SDK, release-pipeline, or
website changes follow a separate maintainer workflow on `main`.

When using a coding agent, follow the [ReasBook contributing skill](CONTRIBUTING/SKILL.md)
as an execution checklist. It mirrors the branch, metadata, validation, and
pull-request rules below without replacing this human-facing guide.

## Understand the branch model

ReasBook keeps mathematical source on version branches so each project is
checked against one exact Lean/mathlib release:

- `main` contains the cross-version catalog and shared tooling. Do not add book
  or paper source to `main`.
- An `Active` `vX.Y.Z` branch accepts source contributions and participates in
  release planning.
- An `Empty`, `Frozen`, or `Archived` branch requires maintainer direction
  before you target it.

Use [`config/toolchains.yml`](config/toolchains.yml) as the branch registry;
do not copy a hard-coded version list from this document. The target branch,
its `ReasBook/lean-toolchain`, your PR title, and any metadata must name the
same version. If the exact version is not registered as `Active`, ask a
maintainer instead of choosing a nearby version.

## 1. Fork and create a contribution branch

Add the official repository as `upstream` once, fetch it, and branch from the
latest target version:

```bash
git remote add upstream https://github.com/optpku/ReasBook.git
git fetch upstream --prune
git switch -c book/<project-slug>-vX.Y.Z upstream/vX.Y.Z
```

For a paper, use `paper/<project-slug>-vX.Y.Z`. Branch slugs use lowercase
letters, digits, and hyphens. Before editing, verify the checked-out toolchain:

```bash
cat ReasBook/lean-toolchain
git branch --show-current
```

If `upstream` already exists, do not run `git remote add` again. Confirm its
URL with `git remote -v` instead.

## 2. Add or update one project

Keep the change scoped to one project unless the PR explicitly coordinates a
shared fix.

| Kind | Project directory | Documentation root | Branch prefix | PR label |
| --- | --- | --- | --- | --- |
| Book | `ReasBook/Books/<ProjectId>/` | `Book.lean` | `book/` | `[Book]` |
| Paper | `ReasBook/Papers/<ProjectId>/` | `Paper.lean` | `paper/` | `[Paper]` |

Book IDs follow `<Title>_<AuthorLastName>_<Year>`, for example
`Analysis2_Tao_2022`. Preserve the spelling and case of an existing project
ID when updating it.

The root `Book.lean` or `Paper.lean` must import the complete public surface
that should be checked and documented. Follow the target branch's existing
`ReasBook/lakefile.lean` registration style: some branches use shared
`Books`/`Papers` libraries, while others register one `lean_lib` per project.
Do not copy a `lakefile.lean` entry from a different toolchain branch without
checking the local layout.

Keep every unrelated book and paper intact. Do not commit generated files,
including `.lake/`, `_site/`, caches, logs, or compiled Lean artifacts.

## 3. Document the contribution

### Required Lean code-author headers

**Every `.lean` file published on GitHub must include verified code authors in
its opening file header. Missing or unresolved attribution blocks submission
and publication, even when the code builds.** This applies to roots, imports-only
aggregators, compatibility modules, generated Lean files, and shared tooling as
well as mathematical proofs. A README, paper citation, or Git log is not a
substitute for the file header.

Follow the [mathlib header convention](https://leanprover-community.github.io/contribute/style.html#header-and-imports):

```lean
/-
Copyright (c) <year> <verified copyright holder>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <verified Lean code author>, <another verified Lean code author>
-/
```

Place this ordinary comment before `module` and imports. Use `Authors` even for
one author, separate names with commas, and do not end the author list with a
period. Replace the template fields with verified information; never publish
placeholders. Respect the original license of reused code rather than changing
it to match the example.

Code authors and bibliographic authors are different roles. Credit the people
responsible for the Lean development, verified from existing notices, original
source repositories, contribution records, or maintainer confirmation. Do not
copy a textbook's author list or infer a human identity from an automation
commit. Preserve existing names, copyright ownership, and third-party notices.
For legacy files, restore verified author information without inventing
copyright ownership. A project-wide roster may be used only with maintainer
confirmation, with its project-level scope stated explicitly. Fix code
generators too, so regeneration does not erase these notices.

Each project-level fallback must cite its evidence in the header, including the
repository, branch or commit, README path and section, for example
`Project-level attribution: <owner>/<repo>@<ref>:<README path> (<section>)`.
Read third-party notices and pinned upstream source before applying a project
roster. Imported files retain the upstream authors, not just the importing
project's contributor names. Attribute local adaptations separately, keeping
both the upstream credit and the scope/source of any confirmed local roster.

Run the checker kept on `main` against the actual source checkout (Python 3.11+):

```bash
python3.11 /path/to/ReasBook-main/scripts/config/check_lean_authors.py \
  --repo /path/to/contribution-checkout \
  --path ReasBook/Books/<ProjectId>
# For papers, use ReasBook/Papers/<ProjectId> and any sibling .lean facade.
```

Omit `--path` to check all first-party Lean files. The checker includes tracked
and non-ignored untracked source, not downloaded dependencies. It verifies the
presence of concrete names; reviewers must still verify who those names refer
to. List unresolved files and ask a maintainer before publication.

### Project documentation

Every project directory needs a `README.md` containing:

- full title, authors, edition, and year where applicable;
- contributor names and GitHub usernames;
- the exact Lean toolchain;
- the covered and intentionally uncovered material;
- declaration and Lean source counts; and
- proof completion plus truthful `sorry` and `admit` counts.

Books also use `book.yml` on branches where book metadata is enabled. Match
the existing files on that branch. When the template and validator are
available, copy [`config/book.yml.example`](config/book.yml.example), use
`null` for unknown values, and validate from the repository root with Python
3.11 or newer:

```bash
python3.11 -m venv .venv
. .venv/bin/activate
python -m pip install -r scripts/config/requirements.txt
python scripts/config/validate_book.py \
  ReasBook/Books/<ProjectId>/book.yml \
  --toolchain ReasBook/lean-toolchain
```

Do not invent statistics or bibliographic values. Paper metadata currently
lives in the paper `README.md`; there is no `paper.yml` contract.

### Required companion update to the main README

**When you add or update a project on a version branch, also synchronize its
corresponding entry in the `main` README. Updating the source branch alone is
not enough if the catalog still describes the old state.**

On a separate branch based on current upstream `main`, inspect `README.md`
and `README.zh-CN.md` using the exact project ID. Update the affected entry in
both languages and its catalog-folder README, if applicable. Check:

- source links and the exact available version branches;
- verified Lean code contributors, separate from bibliographic authors;
- coverage, proof-completion information, and distinct proof routes where listed;
- Docs, Verso, and theorem-map links and their actual publication status.

Preserve other projects, existing version links, and curated catalog structure.
Do not mark future documentation or theorem maps as already published. If a
source-only correction changes none of the catalog facts, record the entry
reviewed and why no README edit was necessary instead of making an empty edit.

Keep this companion change README/catalog-only and target its PR at `main`.
Keep the mathematical source PR targeted at `vX.Y.Z`; do not merge a whole
version branch into `main` to synchronize the README. Cross-link the two PRs
when opening them, or provide both local change sets when PR creation has not
been requested. Report any pending catalog synchronization explicitly rather
than treating the source contribution as fully complete.

## 4. Run focused validation

From the Lean project directory, obtain the optional mathlib cache and check
the project root directly:

```bash
cd ReasBook
lake exe cache get
lake env lean Books/<ProjectId>/Book.lean
```

For a paper, replace the last command with:

```bash
lake env lean Papers/<ProjectId>/Paper.lean
```

`lake exe cache get` only reduces compilation work; a cache-download failure
does not determine whether the source is correct. If the branch defines a
dedicated project library, `lake build <ProjectId>` is a useful additional
check. A repository-wide `lake build` is optional and can be expensive.
Maintainers run the authoritative incremental full build remotely.

Return to the repository root and inspect the complete diff:

```bash
cd ..
git diff --stat upstream/vX.Y.Z...HEAD
git diff --name-status upstream/vX.Y.Z...HEAD
git diff --diff-filter=D --name-status upstream/vX.Y.Z...HEAD
```

The deletion-only command should not show files from unrelated projects.

## 5. Open the pull request

Set the source PR base to the exact version branch, never `main`. The required
companion README/catalog PR targets `main` separately, as described above.

```text
[Book][vX.Y.Z] Add <ProjectId>
[Book][vX.Y.Z] Update <ProjectId>: <short scope>
[Paper][vX.Y.Z] Add <ProjectId>
[Paper][vX.Y.Z] Update <ProjectId>: <short scope>
```

Use this PR body and remove fields that do not apply:

```markdown
## ReasBook contribution report

- **Kind:** Book / Paper
- **Title:** <full title>
- **Project ID:** `<ProjectId>`
- **Contributor:** <name> (@<GitHub-ID>)
- **Code authorship:** every Lean file has verified `Authors:`; check command and result: <details>
- **Target branch:** `vX.Y.Z`
- **Lean toolchain:** `<full content of ReasBook/lean-toolchain>`
- **Declarations:** <total> (theorem/lemma/example: <count>; other: <count>)
- **Lean source:** <file-count> `.lean` files, <line-count> lines
- **Proof completion:** <done> / <total> = <percent>%
- **Remaining placeholders:** `sorry`: <count>; `admit`: <count>
- **Metadata:** project `README.md` added or updated; `book.yml` validated / not applicable
- **Main README synchronization:** affected project entry; `README.md` / `README.zh-CN.md` and catalog files updated; companion change set or PR (or evidence that no catalog facts changed)

### Scope

<Describe the covered material, important design choices, and known gaps.>

### Local validation

<List each command run and its result.>
```

GitHub workflow coverage differs between version branches, so do not assume a
PR job has started merely because the PR is open. Any required status checks
shown by GitHub must pass. Maintainers use the incremental build SDK and the
configured remote build service for the authoritative full build; contributors
should not generate or commit repository-wide caches.

## Pre-submission checklist

- The branch starts from the latest `upstream/vX.Y.Z`.
- The PR base, PR title, `lean-toolchain`, and metadata agree on the version.
- The project path, root file, branch name, and PR label match its kind.
- The project README and contributor information are complete.
- The corresponding `main` README entry is synchronized in both languages,
  including any affected catalog-folder README; the companion change set or PR
  is identified, or the no-change review is explicitly justified.
- Every Lean file has a verified code-author header; existing notices survive
  regeneration, and the author-header check passes. No unresolved attribution
  is being deferred until after publication.
- Focused Lean validation passes and its exact command is in the PR body.
- Statistics and `sorry`/`admit` counts are truthful.
- Unrelated projects are unchanged and no generated output is committed.

## After submission

Respond to review and required checks without rebasing onto a different
toolchain branch. After merge, maintainers pin the version-branch commit in a
future `ReleaseSpec`, build and verify it with the configured remote build
service, and publish an immutable static bundle. Merging a source PR does not
itself rebuild GitHub Pages.
