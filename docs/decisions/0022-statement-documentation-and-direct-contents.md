# ADR-0022: Source-backed statements and direct reading links

## Status

Accepted

## Context

`recall` and `#check` reuse declarations already present in mathlib. They do not
create declarations in the current module, so doc-gen can publish an empty
`main` even though the Lean source contains useful mathematical content. Item
readers previously made users follow a book/paper index, another item index,
and then a documentation link which could lead to that empty page.

## Decision

- Label reading links **Documentation** and mathematical content **Statements**.
  Keep technical identifiers and actual service API routes unchanged.
- Enrich project-owned doc-gen pages in the private build stage, before link
  closure and atomic publication. Display the original source body for modules
  containing `recall` or `#check`, retaining mathematical comments, namespaces,
  variables, and notation. Escape source as text. This is not inferred Lean
  output: a checked expression is not presented as a newly proved theorem.
- Keep existing declarations, anchors, and immutable source links. Never rewrite
  version-branch mathematics or introduce alias theorems just for documentation.
- Give imports-only documentation pages direct links to reachable content,
  following the module graph within shared selected-root ownership. Skip empty
  leaves, deduplicate paths, bound cycles, and sort item numbers naturally.
- Put item documentation/source links on book and paper home pages, with chapter
  grouping. Existing chapter and grouped-item routes remain optional navigation
  and retain their ownership/fragment contracts. Known placeholder items with
  only external imports are labelled as having no statement and link to source.
- Project bookmarks under `sites/<slug>/` open their existing reading entry
  (or documentation when no reading entry exists). Only aggregate catalogs
  return to the README. Split paper sections link directly to their parts.
- Bind the statement renderer to the rendered-doc cache identity. Reuse a
  compatible database analysis checkpoint, but regenerate old HTML. Include the
  renderer in the existing SDK tooling snapshot and its digest.

## Consequences

Both supported doc-gen modes can show referenced mathematics without building
all mathlib documentation or creating an additional literate target per item.
`#check` expressions remain exact source evidence; this change does not extract
the inferred type from Lean's diagnostic output. Ordinary declaration pages keep
their existing rendering. New releases must be built and promoted for the live
website to change; immutable published artifacts are not edited in place.
