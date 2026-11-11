# Theorem Graph SDK

theorem-graph-sdk turns Lean declaration metadata into a stable,
literature-oriented theorem dependency graph. It owns graph analysis,
extraction, rendering, publication, the Lean extractor, and static frontend
resources. It has no task-scheduler dependency.

The architecture has three replaceable layers:

- analysis: pure parsing, representative selection, and helper-dependency
  contraction;
- extractor: a protocol plus compiled-environment and source fallback
  implementations;
- render/generator: JSON, static assets, catalog generation, and atomic
  publication.

## CLI

From this repository, a generated map can be built with:

    ./sdk/theorem_graph/bin/theorem-graph \
      --repo-root . --site-root ReasBookWeb/_site --branch v4.32.2

Curated projects are copied by default. To generate maps for projects without a
curated theorem-map directory, opt in explicitly:

    ./sdk/theorem_graph/bin/theorem-graph \
      --repo-root . --site-root ReasBookWeb/_site --branch v4.32.2 \
      --include-generic

Every rendered map contains `release-context.json`. Its `project` object is the
authoritative release identity: project id and kind, display branch, immutable
commit, repository, and source root. The same object is written to
`metadata.json` (and to `data.json` for generated maps). Source links use the
commit, never the mutable branch. Curated maps that expose the legacy
`LEAN_REF`, `LEAN_COMMIT`, and `LEAN_BASE` variables are normalized at render
time, so authors do not hand-edit release commits in static assets.

The packaged resources are used by default; `--extractor` and `--assets`
allow explicit replacements. Compiled projects are extracted serially, with a
fresh Lean process and environment for each project. A failed project can fall
back independently without discarding compiled evidence from its siblings.
Compiled extraction failures fall back to source comments unless
`--no-source-fallback` is supplied. The output tree is staged and atomically
replaced, so a failed run leaves the previous published tree intact. Use
`--extractor-timeout-seconds` to bound each project's compiled-environment
extraction.

The CLI streams project extraction, source-inventory and rendering progress to
stderr, including completed-project durations. With `--json`, stdout remains
one final machine-readable report. Callers running several projects must allow
the sum of their extraction deadlines plus time for inventory and publication.

Generated `data.json` files use schema version 2. Every item keeps the legacy
`dependencies` union and also records two provenance-preserving edge lists:

- `statementDependencies`: dependencies originating in the declaration type
  (the theorem statement);
- `proofDependencies`: dependencies originating in the proof term or, for a
  definition, its implementation body.

Helper declarations are contracted to the nearest literature-labelled item,
but the originating statement/proof class is retained. Source fallback cannot
recover elaborated constant references, so both typed lists and the legacy
union are empty in that mode. `generation.mode` and `generation.fallbackReason`
make this limitation explicit rather than presenting an empty graph as
compiled evidence.

Literature labels may start with a chapter prefix, for example
`Chapter01 Theorem 1.2.10`; extra-item suffixes such as `14.6-extra-1` remain
part of the item identity. `Helper for Chapter01 ...` is not a literature
label. A label-parser correction can reuse pinned raw Lean exports, provided
each isolated environment is contracted separately before merging. It does
not recover dependencies from source modules that never compiled.

A successful compiled run is overlaid on a complete labelled source inventory.
The merge is keyed by the stable literature item ID: compiled records remain
authoritative on overlap, compiled-only records are retained, and declarations
omitted by the aggregate root remain visible with
`dependencyEvidence: "source-only"` and no inferred edges. The `generation`
object reports `compiledItemCount`, `sourceInventoryItemCount`,
`sourceOnlyItemCount`, `compiledOnlyItemCount`, `mergedItemCount`, and
`dependencyCoverage`, so partial coverage is explicit rather than silently
dropping nodes.

## Existing compiled modules outside an aggregate root

`isolated` inventories all source-owned modules and reads the `.olean` files
already present in a compiled search root. It never invokes Lake or compiles
aggregate modules, and writes only to a new, disjoint output directory:

```bash
./sdk/theorem_graph/bin/theorem-graph isolated \
  --project-root /source/ReasBook/Books/Example \
  --project-id Example --module-prefix Example \
  --compiled-root /cache/lake/build/lib/lean \
  --search-path /cache/lake/packages/mathlib/.lake/build/lib/lean \
  --lean-bin /toolchains/lean-v4.30.0/bin/lean \
  --output /runs/example-isolated --branch v4.30.0 --commit FULL_COMMIT \
  --batch-size 16 --jobs 4 --memory-mb 12288 --memory-budget-mb 49152
```

Repeat `--search-path` for **every** required dependency package's compiled
library directory, preserving the package environment's paths. These paths can
be inventoried directly under the existing `.lake/packages/*/.lake/build/lib/lean`
without running `lake env`. Source, compiled libraries and toolchain must be
from the same version and source identity; the supplied commit is recorded but
this command does not certify arbitrary external artifacts. Use `--plan` with
the same arguments to list available and missing modules without writing files
or starting Lean. Missing `.olean` files need compilation elsewhere before this
command can extract their declarations.

Each Lean process uses one thread and an explicit allocator limit (`-M`);
that limit is **not** a hard RSS limit. Reserve additional Pod memory for mapped
imports and Python. Parallel jobs require an explicit allocator memory budget
at least `jobs × memory-mb`. Independent batches run concurrently; failed batches
split sequentially into smaller environments. Every attempt retains a log,
configuration, return code, UTC timestamps and elapsed time. `progress.json`
records missing, completed and failed modules; `result.json` records total wall
time. Existing output directories are rejected; retries use a new output.

The runner contracts each environment's helpers before merging literature
items using `merge_compiled_graphs`. It never merges incompatible raw declaration
dictionaries, which would mix unrelated same-named helpers. The map in `map/`
is always explicitly marked `lean-environment-partial`; source-only entries
remain visible, and a successful command is not proof that the whole book was
compiled or that every environment succeeded. If no environment succeeds, the
command fails and retains diagnostics without publishing a map.

## Python API

    from pathlib import Path
    from theorem_graph_sdk import GraphGenerator, TheoremGraphConfig

    config = TheoremGraphConfig(
        repo_root=Path("."),
        site_root=Path("ReasBookWeb/_site"),
        branch="v4.32.2",
    )
    report = GraphGenerator(config).generate()

For tests or a different extraction service, pass an object implementing
DeclarationExtractor to GraphGenerator(extractor=...). The extractor only
returns JSON-compatible declaration records; it never edits Lean source files.

Rebuild a catalog after merging branch artifacts with:

    ./sdk/theorem_graph/bin/theorem-graph catalog --site-root .site
