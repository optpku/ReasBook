# ADR-0022: Source-backed statements and direct reading links

## Status

Accepted; revised after the static-site click-path audit. Supersedes the
link-only reader content policy in ADR-0009, preserving its route ownership
and isolated-fragment contracts.

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
  closure and atomic publication. Display command/signature excerpts for modules
  containing `recall` or `#check`, retaining mathematical comments and explicit
  variable/namespace/notation context. Omit proof bodies and unrelated helpers;
  do not paste the whole source file. Escape source as text. This is not inferred Lean
  output: a checked expression is not presented as a newly proved theorem.
- For numbered item previews, prefer comments beginning with the exact item
  identifier (optionally after a `Chapter10` prefix), treating dots and hyphens
  in the number equivalently. Exact headings always rank first. Among other
  comments, explicit `Helper`/`Auxiliary` prefixes rank last; these words within
  mathematical prose (e.g. "auxiliary objective") do not affect priority.
  Preserve source order within a rank. Keep complete `structure`/`class` fields and `inductive` constructors,
  including field defaults: those bodies are part of the mathematical definition.
- Track `mutual` as a command/block boundary, not namespace context. Its `end`
  must close that block without discarding the enclosing variables or notation.
- Keep existing declarations, anchors, and immutable source links. Never rewrite
  version-branch mathematics or introduce alias theorems just for documentation.
- Give imports-only documentation pages direct links to reachable content,
  following the module graph within shared selected-root ownership. Skip empty
  leaves, deduplicate paths, bound cycles, and sort item numbers naturally before
  statement kinds, within their chapter/module groups.
- README reading links go to the named project page. A single-project build's
  root contains that same page and project title, not the shared ReasBook hub.
- Book home pages link to stable item anchors in chapters. Chapters contain
  numbered source statement previews with secondary Documentation/source links.
  Section-oriented chapters inline their sections' statement excerpts, including
  split parts, instead of adding another aggregation hop. The sidebar links
  directly to these real chapter pages and stays at chapter depth. Legacy
  chapter routes remain compatible real pages, not required redirect hops.
- Item papers show statements directly on their home page. Papers without
  separate sections expose excerpts from reachable project-owned modules, so
  BFGS and RockafellarSum are not dead ends. Split-section home links go straight
  to parts; old split-section pages also contain statement excerpts.
- Numbered facades can contain only derived consequences while their defining
  clauses live in imported owner modules. Reviewed selectors in
  `ReasBookWeb/scripts/statement_previews.py` identify the defining clauses of
  the four affected TR-LALM items. Render their exact source, retain the item
  anchor, link each clause to its own module, and explicitly label the preview
  as partial. Missing or ambiguous selectors fail generation rather than
  silently substituting the first helper.
- Known placeholders with only external imports have no documentation link and
  say `no statement yet`. Internal facades resolve to reachable statements with
  the actual excerpt's source link. Unsupported source commands explicitly say
  `statement preview unavailable`; they are not silently called empty or proved.
- Only direct chapter children qualify as ordinary sections. Nested item support
  files such as Sun–Yuan's `Lemma_13_6_3/section13325` never become sidebar sections.
- Use bibliographic project titles and the same root module passed to the
  documentation builder. Explicit Lake `roots` are not a reliable substitute:
  BFGS retains a real `BFGSMinimumQOrder_Liu_2026` aggregate module selected for
  Docs, while the separate `Paper` module is outside that build's import closure.
  Register that aggregate as its own Lake library rooted at `Papers`, and keep
  the original flat-source roots in `BFGSMinimumQOrder_Implementation`. A file
  discovered by the documentation scanner is not proof that Lake builds it:
  validate that the public target produces the aggregate `.olean` as well.
- Project bookmarks under `sites/<slug>/` open their existing reading entry
  (or documentation when no reading entry exists). Aggregate static catalogs
  stay on the static site and only link to existing artifacts; they no longer
  redirect to the README. Pages projection rebuilds these catalogs against its
  retained routes, including documentation-only projects.
- Assembly and reader entrypoint generation use the shared, self-contained
  styled catalog renderer in `reasbook_sdk_common.catalog`. The final Pages root
  is written by `PagesSiteProjector._write_catalog_redirects`, using that same
  renderer after selecting retained routes, not a second HTML implementation.
- Counts, navigation labels, transition-page explanations, and hidden tooltips
  do not satisfy the readable-content publication gate.
- Bind the statement renderer to the rendered-doc cache identity. Reuse a
  compatible database analysis checkpoint, but regenerate old HTML. Include the
  renderer in the existing SDK tooling snapshot and its digest.
- Runtime label changes must also be applied to each active version branch's
  `ReasBookWeb/ReasBookSite.lean`. Production uses that version's Lean runtime;
  main's tooling snapshot carries the generator, not a replacement runtime.
  Pin the updated branch commits in a new release plan after these changes are
  committed and merged; do not alter an already frozen plan or release artifact.

## Consequences

Both supported doc-gen modes can show referenced mathematics without building
all mathlib documentation or creating an additional literate target per item.
`#check` expressions remain exact source evidence; this change does not extract
the inferred type from Lean's diagnostic output. Ordinary declaration pages keep
their existing rendering. New releases must be built and promoted for the live
website to change; immutable published artifacts are not edited in place.

The source excerpt scanner is a conservative lexical presentation helper, not
an elaborator. It preserves expressions and separates previews from authoritative
Documentation. It does not infer types, recreate dependencies or certify proofs.
`v4.29.0` is not an active registered release; Klenke and Vogel remain explicitly
excluded. Missing deployments require separate publication work, not fabricated
pages or changing project selection to make a catalog look complete. The mirror's
external hosting inventory must likewise be regenerated from published artifacts.
