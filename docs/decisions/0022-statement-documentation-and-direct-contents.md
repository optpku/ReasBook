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
- Book home pages have a compact chapter directory, followed by the published
  **Formalization contributors** roster with its catalog source. This is
  project-level credit, distinct from textbook authors and file-level Lean
  headers. Bundle the shared roster in the common SDK for isolated release workers;
  consistency tests require exact parity with both main README catalogs.
  The aggregate catalog uses the same roster and preserves distinct upstream
  roles. Each statement card reads the actual selected source's header, not its
  facade's or the generator's authors. Full literate routes receive the same
  source credit below the title in a validated, idempotent post-render step.
  Explicit project-level attribution and its evidence remain visible; missing
  file metadata is not replaced with guessed project membership.
  Catalogs group books and papers and accept explicit project identities so
  attribution survives custom local routes. Flat paper reading routes retain
  their owning project sidebar and a numerically ordered file list. Numbered
  file headings stay short; the browser title retains the project context.
  Native highlighted blocks are keyboard-focusable like plain excerpts.
  Chapters contain
  numbered source statement previews with secondary Documentation/source links.
  Section-oriented chapters inline their sections' statement excerpts, including
  split parts, instead of adding another aggregation hop. The sidebar links
  directly to these real chapter pages and their per-file statement anchors. Legacy
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
- Automatically discovered paper sections must be direct project children named
  `sectionNN` or `sectionNN_partN`. Internal support files such as BFGS's
  `ReasLib/.../SectionContraction` are not reading entries merely because their
  names start with `Section`. Keep explicitly configured reading modules and
  imported facades; check generated Documentation links against the public
  root's actual documentation closure.
- Book and paper statement links use the Build SDK's public-root closure, not the mere
  existence of a source file. Keep source excerpts for numbered legacy items
  outside that closure, label them `source only`, and link to Lean source rather
  than nonexistent Documentation (for example TR-LALM's legacy remarks C.1/C.2).
  Apply the same check to the actual owner of a selected or imported clause.
- Verso statement excerpts slice native SubVerso token trees by exact Unicode
  source ranges. Keep tokens' term/type hovers, structure fields, constructors,
  and source context; exclude proof bodies and proof-state panels. The lexical
  selector chooses the excerpt but never fabricates semantic information.
  Register checked excerpt owners as literate inputs without creating another
  reading page per item. Load only prebuilt JSON, validate it against the actual
  source and displayed excerpt, and fail on stale data instead of quietly
  downgrading checked excerpts to text. Bound the decoded cache to one module.
  Include source/config identity in generated pages so imported type changes
  invalidate Lake's page cache even when the visible signature is unchanged.
  Bundle the runtime and a scoped stylesheet patch with the release tooling so
  private version-branch builds receive the same hover and mobile behavior.
  Set Verso's own semantic color variables for keywords, constants, and local
  variables; keep popovers in the same readable monospace palette. Do not pass
  already highlighted HTML through a second lexical highlighter. A plain-text
  snapshot has no term types: it must be rebuilt from its source's semantic
  data, not described as hover-enabled after a CSS-only refresh. Acceptance
  must exercise actual book chapters, including recall/`#check` entries, and
  check visible variable/constant type popups as well as token colors.
  Older Mathlib/Lean combinations can omit term metadata for the name at the
  head of a `recall` command or for a bare global `#check` identifier. Preserve
  original parser positions before SubVerso adjusts trailing source information,
  then enrich that exact parser span with a native
  constant token, using the recorded command environment, namespace, and open
  declarations and Lean's pretty-printed type. Verify the text is unchanged.
  Never resolve it in a different command's final namespace or
  assign a type based on its spelling. Install this small compatibility hook in
  the private version extractor using owned, validated, idempotent markers.
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

## Numbered reading titles

Use one presentation rule for numbered chapters, sections, subsections, parts,
appendices and named statements, both in the reading body and in directories
and sidebars. Put the number on a separate, smaller line and the actual name
below it. Remove only the separator between that number and name. Long names
wrap naturally; heading levels retain their relative visual hierarchy.

The shared runtime formatter owns this rule for every book and both sidebar
renderers. Retain canonical labels, numbering, destinations, anchor IDs and
accessible navigation names. Move existing name nodes rather than replacing
rich mathematical markup with plain text. Preserve inline links, emphasis and
native Lean hover metadata and prefix anchor aliases; do not apply title
formatting to code, inline citations or statement prose. Unnamed headings such as “Statements” and plain numbered items without a
name remain unchanged. Local previews use the same formatter and styles, and
identify their source snapshot in the preview controls rather than repeating a
banner above every reading title.

## Item-structured paper reading

Paper homes show the existing reader's section groups instead of duplicating
all excerpts. The Items route keeps every statement and its original anchors,
source links, publication scope and Lean author attribution. The shared primary
and fallback sidebar lists paper-level items by number, groups them by section,
and folds supporting implementation-file navigation under a separate disclosure.
Section links remain direct links with separate expansion buttons. Old home
item fragments forward to the same item on the existing reader, preserving
clause suffixes. Share this compatibility path across the primary and fallback
renderers. Supporting-file navigation stays current when a declaration fragment
is selected inside the file. Do not emit redundant `Statements` headings; keep old group
anchors and promote unsectioned item headings to the correct level.

TR-LALM's editorial section labels describe the deterministic method, stochastic
method, second-order correction and appendix remarks. Their evidence is the
pinned source README's Scope and Article-to-Lean Map; they do not claim to quote
manuscript section headings. Local previews reorganize only existing native
artifacts and verify that all mathematical blocks remain on the native reader.
No source, proof, term-type data or author list is inferred or regenerated.

## Consequences

Stable reading-section anchors are empty HTML directives immediately before
document-level headings. Verso does not accept Markdown section headers inside
an HTML directive. This rule applies to book subsections, paper sections and
appendices; native compilation must validate the generated pages as well as
the browser layout.

Book homes separate the registered title from its author/year citation, using
the same typography as curated paper titles. Navigation repeats this hierarchy
and retains the canonical bibliography in its accessible name and browser title.
The complete title and all source URLs remain unchanged. Bibliographic authors
remain distinct from the formalization contributors; chapter and section names
continue to follow the shared number-and-name rule.

Both supported doc-gen modes can show referenced mathematics without building
all mathlib documentation. Native Verso hovers additionally require semantic
extraction for each rendered, checked source module; the existing bounded,
incremental literate stage handles these inputs. This increases first-build
work, but adds no extra navigation layer or per-item reading page.
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
