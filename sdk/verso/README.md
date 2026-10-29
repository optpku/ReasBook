# Verso Build SDK

`verso-build-sdk` builds a Verso/Lake site through a small, explicit pipeline.
It contains no platform integration, so the same package can be used locally,
from CI, or as a stage inside an external build service.

The site generator itself is the upstream
[Lean Verso project](https://github.com/leanprover/verso). This package provides
the transport-neutral planning, execution, and cache boundaries around it; it
does not replace or fork the upstream generator.

The generic site pipeline has two optional stages:

1. run a caller-supplied generator (for example, section/route generation);
2. run `lake` with the requested target arguments.

The toolchain is read from `lean-toolchain` by default and executed through
`elan run --install`. Commands are argv arrays rather than shell strings, and
the runner is injectable for tests or another execution service.

Large ReasBook sites also use `verso-literate`, a separate cache capability in
this SDK. It consumes the generator's deterministic module manifest, builds
independent `+Module:literate` targets in bounded parallel batches, validates
the JSON/Lake trace artifacts, and atomically records a source-identity-bound
completion marker. A repeat run performs no Lake command when the exact marker
and artifact hashes still match. Successful batches are committed to a second,
identity-bound progress marker, so a retry schedules only unfinished modules.
Both local and remote callers are serialized by a cache-local lock.

ReasBook's generated statement readers use this same semantic cache for native
Lean term/type hovers. The module manifest includes checked excerpt owners as
well as full literate pages; it is not a page inventory. The generator copies
`ReasBookWeb/scripts/statement_code.lean` into the private Web source tree. Its
code block selects original SubVerso tokens by exact source ranges, verifies the
source and displayed text, and renders with Verso's native hover support. Proofs
stay omitted. Files outside the public documentation root remain source-only.
The bundled `statement_code.css` is installed in an owned block of the private
Web tree's stylesheet, preserving each version branch's theme while ensuring
native code scrolls within its block on mobile and contributor lists wrap.
The palette uses Verso's semantic token classes for keywords, constants, and
local variables, including inside type popovers. Plain-source snapshots do not
gain type information from this stylesheet; rebuild their chapter modules and
semantic inputs before testing hover on the actual reading routes.
The generator also installs `recall_info.lean` in three owned blocks of the
version's `LiterateExtract.lean`. It preserves original parser positions before
SubVerso adjusts trailing source information. It enriches the recalled-name
or bare global `#check` identifier's
span with a native constant token, using that command's recorded Lean environment,
namespace, open declarations, and Lean's pretty-printed type; the text is unchanged.
Section-local `#check` variables keep their native term metadata.
It does not guess names or types, replace Mathlib, or change the mathematical
source. Existing version-specific compatibility code is retained; an unsupported
extractor shape fails generation instead of silently omitting the fix.
Source/config fingerprints in generated pages prevent reusing old hovers after
imported types change. A first build requires more extraction work; use the
existing bounded parallel cache stage, not per-item nested Lake invocations.

Project catalogs and homes share `reasbook_sdk_common/project_contributors.json`;
its rosters must match both main READMEs, including upstream contribution roles.
Statement cards instead read the actual selected source file's opening author
header. Missing authors stay explicitly unrecorded; a project roster is never
silently substituted. Project-level attribution remains labeled as such.
The generator also emits `.reader-attributions.json` from the actual route
bindings. After rendering, `scripts/build/verso.sh` applies
`ReasBookWeb/scripts/reader_attributions.py` to full literate pages (and aliases)
before fragment validation. This adds source credit beneath the title without
changing native hover markup. Missing pages, unsafe targets or ambiguous markers
fail the build. Direct SDK-only renders must run this post-step before publishing.

The opt-in `tests/test_statement_hover_native.py` acceptance test runs a real
matching Lean extractor and Verso renderer, then checks visible type popups in
Chromium, stale-data failures, and mobile layout. Set `REASBOOK_HOVER_LEAN`,
`REASBOOK_HOVER_WEB_CACHE` (built dependency packages), and
`REASBOOK_HOVER_EXTRACTOR` (that version's `LiterateExtract.lean`); run
`python -m unittest tests.test_statement_hover_native -v` with Playwright
available. Set `TMPDIR` to a private persistent workspace directory, or preserve
the result with `REASBOOK_HOVER_OUTPUT` pointing to a new directory. No shared
dependency cache is modified. Normal unit-test runs skip this native canary.

## CLI

```bash
./sdk/verso/bin/verso-build /path/to/ReasBookWeb \
  --generator 'python3.11 scripts/gen_sections.py' \
  --target exe --target reasbook-site \
  --dry-run

./sdk/verso/bin/verso-literate \
  --lean-root /path/to/ReasBook \
  --module-manifest /path/to/ReasBookWeb/.literate-modules.json \
  --jobs 4 --validation-jobs 4 --chunk-size 32
```

Install the package in editable mode when using the console entry point:

```bash
python3.11 -m pip install -e sdk/common -e sdk/verso
verso-build /path/to/site --generator 'python3.11 scripts/gen_sections.py'
```

Useful environment settings use the `VERSO_` prefix: `VERSO_TOOLCHAIN`,
`VERSO_LAKE_BIN`, `VERSO_ELAN_BIN`, `VERSO_TARGETS`, `VERSO_GENERATOR`,
`VERSO_OUTPUT_DIR`, and `VERSO_VERIFY_OUTPUT`. `VERSO_ENV_<NAME>` adds an
explicit build environment variable. Credentials and platform-specific values
are intentionally outside this SDK.

When `VERSO_OUTPUT_DIR` or `--output-dir` is set, the SDK resolves it to an
absolute path and passes it to Verso as `--output`; the environment variable is
not consumed by the generated Lean executable itself. Do not also put an
explicit `--output` in `VERSO_TARGETS`: the SDK rejects that ambiguous
combination instead of relying on option order.

`verso-literate` accepts `REASBOOK_BUILD_LAKE_BIN`,
`REASBOOK_LITERATE_JOBS`, `REASBOOK_LITERATE_VALIDATION_JOBS`,
`REASBOOK_LITERATE_CHUNK_SIZE`, and
`REASBOOK_LITERATE_BATCH_TIMEOUT_SECONDS`. Release finalizers additionally
pin the cache identity with `REASBOOK_GITHUB_BRANCH`,
`REASBOOK_SOURCE_COMMIT`, `REASBOOK_LAKE_MANIFEST_SHA256`,
`VERSO_TOOLCHAIN`, and `REASBOOK_CACHE_ARCHITECTURE`, plus the finalizer's
`REASBOOK_TOOLING_SHA256`; ordinary local runs derive missing identity fields
from the checked-out Lean project and helper implementation. The helper always
hashes the actual Lean source tree and checks supplied commit, manifest, and
toolchain claims against local files, then rechecks source/module digests
before every progress checkpoint and final completion.
`REASBOOK_LITERATE_ADOPT_EXISTING=1` is
reserved for an orchestrator that has independently locked and verified the
exact immutable cache key; the release orchestrator provides that gate.
It applies only when neither completion nor progress state has ever existed,
so stale or corrupt state can never be relabeled as a new identity.

Lake does not provide an outer `-j` option. As a generated Lean executable it
uses `LEAN_NUM_THREADS` to size its runtime task manager; `LAKE_JOBS` is not a
Lake setting. `--jobs` is therefore only Lake's runtime worker count; it does
not by itself define a total CPU budget, create an allocation, or control the
`-j` arguments inherited by child Lean compilers from the package. The helper
sets `LEAN_NUM_THREADS`, removes any inherited `LAKE_JOBS`, and reports the
child setting as `source-configured`. An orchestrator claiming a total budget
must also account for package `moreLeanArgs` and enforce the real allocation
or CPU affinity. Changing those source arguments can invalidate Lake traces,
so the generic SDK never rewrites a caller-owned lakefile.
Large generated JSON files are verified with an iterative mmap-backed grammar
parser, so validation does not build a Python object tree. Mapped pages may
still appear in RSS up to roughly the current artifact size and are validated
only after the Lake subprocess exits. `--validation-jobs` independently
controls a spawn-based process pool for that CPU-heavy, read-only post-batch
validation. The generic SDK defaults to one worker and accepts at most eight;
the full release finalizer explicitly uses four, while smaller canaries cap the
pool by their configured CPU width. Outputs are submitted largest first but
consumed in module-manifest order, and a progress checkpoint advances only
after the entire batch validates. Completion-marker, progress-recovery, and
adoption paths remain serial because they include deterministic repair or
deletion behavior. Validation width does not affect cache identity or Lake
traces. Python API callers using more than one validation worker must invoke
the builder from a normal guarded entry point so the `spawn` start method can
safely import the main module.

## Python API

```python
from pathlib import Path
from verso_build_sdk import VersoBuildConfig, VersoBuilder

config = VersoBuildConfig(
    web_root=Path("ReasBookWeb"),
    generator=("python3", "scripts/gen_sections.py"),
    targets=("exe", "reasbook-site"),
)
result = VersoBuilder(config).run(dry_run=True)
```

Use `VersoBuilder(..., runner=...)` to supply a fake or remote command runner.
