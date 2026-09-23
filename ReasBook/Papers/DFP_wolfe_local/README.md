# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Venue:** arXiv:2608.21708v1 (`math.OC`), 2026
- **Paper ID:** `DFP_wolfe_local`
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1)
- **Source development:** [imathwy/DFP_wolfe_local](https://github.com/imathwy/DFP_wolfe_local)
- **Source snapshot:** [`c60a034d0e45d46596941b3f3ab967ed9491f1f0`](https://github.com/imathwy/DFP_wolfe_local/commit/c60a034d0e45d46596941b3f3ab967ed9491f1f0)

## Contributor

- Zichen Wang ([@imathwy](https://github.com/imathwy))

## Coverage

This paper formalization develops a uniformly convex, globally Hessian-bounded
counterexample for the classical inverse-form Davidon-Fletcher-Powell (DFP)
method. The public `DFPWolfe` surface covers:

- the planar and all-dimensional counterexamples;
- the standard weak-Wolfe and paper-range strong-Wolfe interfaces;
- the global and level-set formulations of the convergence predicate;
- the two-phase orbit, limiting-circle, separation, and bump-extension
  constructions;
- the identity-initialized operator and matrix `liminf` certificates;
- a global one-half Hölder Hessian bound for the same strong-Wolfe
  counterexample in every dimension at least two, preserved under identity
  initialization;
- failure of every Hölder exponent greater than one half on the counterexample's
  initial sublevel, including its higher-dimensional extensions;
- planar convergence under weak or strong Wolfe conditions from arbitrary
  initial positive-definite matrices, assuming local Hessian Lipschitz
  regularity near the initial sublevel, together with the `C³` corollary; and
- the general planar secant degeneration lemma, including the adjacent-step
  product bound, uniform matrix boundedness, and vanishing smallest eigenvalue.

This update includes the convergence and Hölder-regularity results from the
revised manuscript accompanying the source snapshot above; the arXiv link
identifies the original paper.

The development also includes the reusable `ReasLib` analysis, topology,
calculus, and DFP infrastructure needed by these statements. Numerical
experiments and manuscript presentation files are kept locally and are not
tracked in either Lean source repository.
The implementation roots remain under this project directory while dedicated
Lake libraries preserve their public `DFPWolfe` and `ReasLib` module names.

## Statistics

The counts below cover the project's tracked Lean source files, including the
`DFPWolfe` and `ReasLib` implementation roots, their aggregate roots, and the
`Paper.lean` wrapper.

- **Lean code:** 448 `.lean` files, 113,947 physical lines, 107,132 nonblank lines
- **Declarations:** 3,707 (theorem/lemma: 3,156; other: 551)
- **Declaration breakdown:** 2,866 theorems, 290 lemmas, 492 definitions,
  3 abbreviations, 51 structures, and 5 instances
- **Module split:** 13 `DFPWolfe` files and 432 `ReasLib` files, plus three root/wrapper files
- **Proof completion:** 3,156 / 3,156 theorem and lemma declarations have no placeholders
- **Remaining placeholders:** `sorry`: 0; `admit`: 0
- **Project-defined axioms:** 0

These are source-level counts of declaration heads, including attributed, private, and
noncomputable declarations, after removing comments and string literals.
They do not count the imported mathlib environment. `Paper.lean` is the
validation root for the complete public surface.

## Main declarations

- `DFP.existsStrongWolfeCounterexample_of_parameterRange`
- `DFP.main_not_globalWeakWolfeConvergence_of_parameterRange`
- `DFP.main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange`
- `DFP.not_PaperRangeGlobalWeakWolfeConvergence`
- `DFP.not_PaperRangeLevelSetGlobalWeakWolfeConvergence`
- `DFP.existsMatrixIdentityLiminfStrongWolfe_of_parameterRange`
- `DFP.existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two`
- `DFP.existsMatrixIdentityLiminfStrongWolfeHolder`
- `DFP.main_planarWeakWolfeConvergence`
- `DFP.main_planarStrongWolfeConvergence`
- `DFP.SecantIteration.planarDegeneration`

## Theorem dependency map

The map has two views: **Paper numbers** shows the revised manuscript's
Theorem 1, Corollary 2, Theorem 3, Proposition 4, and Lemmas 5–11; **Lean
declarations** retains the complete declaration inventory described below.
Use the view switch above the search box, or append `?view=paper` to the
interactive map URL. The numbered view opens as an 11-node overview with
18 dependency edges, exact statements from the paper, and expandable Lean source links.

Numbering follows the September 2026 `main-new.tex` revision and the eleven
[paper navigation modules](DFPWolfe/README.md). Each paper declaration has a
directly discoverable numbered file; its `#check` commands point to the proof
implementation in `DFPWolfe.Main` or `ReasLib`. Each paper node groups reviewed
Lean proof components; some nodes correspond to several separate declarations
or only the specified parts of a result. The node's correspondence panel states
that scope explicitly. Edges are paths in the compiled declaration graph after
unassigned helpers are contracted, not manually inferred paper citations.
The grouping lives in [paper_results.json](tools/paper_results.json), and
[paper-data.json](theorem-map/paper-data.json) retains an explicit declaration
path witnessing each edge. The statement panel quotes each complete theorem
environment from the revised paper, including assumptions, constants,
quantifiers, equations, and resolved cross-references. These quotations describe
the paper's statements; the separate Lean correspondence panel explains which
formal declarations or proof components are linked.

To regenerate just the numbered view from the existing graph, run:

```bash
python3 ReasBook/Papers/DFP_wolfe_local/tools/generate_paper_graph.py
```

Optionally pass `--manuscript /path/to/main-new.tex` to check all eleven
environment types, numbers, and TeX labels against the local manuscript. The
manuscript is not copied into this repository. Full graph regeneration also
regenerates this numbered projection and preserves the view switch.

Exact excerpts, source line ranges, and SHA-256 values are stored in
[paper-statements.json](theorem-map/paper-statements.json). The panel also exposes
the original LaTeX. After a manuscript change, compile it to obtain current
cross-reference numbers, then re-extract and regenerate:

```bash
python3 ReasBook/Papers/DFP_wolfe_local/tools/extract_paper_statements.py \
  --manuscript /path/to/main-new.tex --aux /path/to/main-new.aux \
  --renderer node ReasBook/Papers/DFP_wolfe_local/tools/render_paper_math.cjs \
  /path/to/katex/dist/katex.js
python3 ReasBook/Papers/DFP_wolfe_local/tools/generate_paper_graph.py \
  --manuscript /path/to/main-new.tex
```

Extraction uses Pandoc and KaTeX 0.16.22 in strict mode. Only typography,
cross-reference resolution, and display-equation layout are transformed; prose
is not rewritten. Rendered HTML/MathML, CSS, and fonts are served locally, so
mathematical statements do not depend on a third-party CDN.

Following the ReasBook Reviewer layout, each numbered result displays the
original paper statement above **Corresponding Lean code**, before the
dependency lists. The code block includes the declaration and its proof,
syntax colors, a copy button, and a GitHub source-range link. A selector exposes
all linked declarations when a paper result has several formal components;
the correspondence note keeps their coverage explicit.

[paper-lean.json](theorem-map/paper-lean.json) contains 32 exact source excerpts.
Their end positions come from the compiled doc-gen4 database, and every source
file is checked against the documentation manifest's SHA-256 before slicing.
Regenerate after a source change with:

```bash
python3 ReasBook/Papers/DFP_wolfe_local/tools/extract_paper_lean.py \
  --docs-root /path/to/verified/project-docs
```

Full graph regeneration with `--docs-root` extracts fresh code from the same
source commit; without it, stale excerpts are rejected. Both modes retain the
code-panel assets. The syntax highlighter is adapted from ReasBook Reviewer and escapes
source text; it changes presentation only.

The [interactive theorem map](theorem-map/index.html) and its
[machine-readable graph](theorem-map/data.json) cover the refactored formalization
at ReasBook commit `2d35734871c7f1dc028c4f1c376e17fcfe062443` on `v4.32.0`.
All 2,565 public source-declared theorems and lemmas have dependencies extracted
from the compiled `DFP_wolfe_local.Paper` environment. There are 7,292 distinct
directed dependency edges and zero source-only inventory entries. Private
lemmas account for the difference from the declaration-head statistics above.

The main-results group includes planar weak/strong Wolfe convergence, general
secant degeneration, sharp one-half Hölder regularity, and identity
initialization. Statement dependencies and proof dependencies are distinguished.
Definitions, private helpers, and compiler-generated declarations are contracted
using the ReasBook theorem graph SDK. Mathlib dependencies are outside this
project graph. Source links point to exact declaration lines in the immutable
source commit. The numbered view uses current manuscript numbers; the full graph uses Lean
declaration names as stable identities.

GitHub displays the HTML source rather than executing the interactive viewer.
For local browsing, run this command from the repository root and open
`http://localhost:8000`:

```bash
python3 -m http.server 8000 --directory ReasBook/Papers/DFP_wolfe_local/theorem-map
```

The directory follows the SDK's project-owned `theorem-map/` convention and can
be copied into a future ReasBook site release. Adding it to the source branch
does not itself deploy GitHub Pages.

To reproduce the graph with Python 3.11+ and a current ReasBook SDK checkout,
first check `Paper.lean` as below, then run from the repository root:

```bash
python3.11 ReasBook/Papers/DFP_wolfe_local/tools/generate_theorem_map.py \
  --sdk-root /path/to/ReasBook/sdk/theorem_graph \
  --output /tmp/dfp-theorem-map-new \
  --evidence /tmp/dfp-theorem-map-evidence-new \
  --docs-root /path/to/verified/project-docs
```

Both output paths must be new. The evidence directory retains raw exported
declarations, an extraction log, and checksums. It is intentionally not committed.
The adapter includes the `DFPWolfe` and `ReasLib` module roots and handles the
Lean 4.32.0 extractor configuration explicitly. It uses one Lean thread and an
8 GiB Lean allocator limit; imported memory-mapped files can add to process RSS.
For rendering-only changes, `--reuse-evidence` accepts an existing evidence
directory after checking its source, extractor, and raw-data hashes.

## API documentation and Verso reading pages

The refreshed API documentation contains 447 real project-module pages, covering
the complete imported closure of `Paper.lean`. The Verso guide retains its eight
existing reading routes, with `main-theorems` now displaying `DFPWolfe.Main`.
The source excerpts, highlighted reading pages, API source links, and theorem
map refer to the same immutable ReasBook source commit recorded above.

The project adapters use a clean ReasBook SDK checkout and compatible prebuilt
doc-gen4/Verso dependencies. After committing and checking the Lean source, run:

```bash
python3.11 ReasBook/Papers/DFP_wolfe_local/tools/build_docs.py \
  --sdk-root /path/to/ReasBook/sdk --output /tmp/dfp-api-docs-new
python3.11 ReasBook/Papers/DFP_wolfe_local/tools/build_verso.py \
  --tooling-root /path/to/ReasBook \
  --web-cache /path/to/compatible/ReasBookWeb \
  --workspace /tmp/dfp-verso-new
```

Both builders run bounded, serial Lean jobs and never invoke `lake build`.
The Verso adapter re-extracts all eight source modules, copies the matching web
package cache into its disposable workspace, and records source/JSON hashes in
`verso-manifest.json`. [verso_modules.json](tools/verso_modules.json) owns the
module-to-route mapping. Full generated documentation, sites, caches, and logs
stay outside Git; only the curated theorem map and reproducible tools are
checked in. A version-branch PR does not itself publish these outputs: the
website release must replace the DFP Docs, Verso, and theorem-map resources
together after merge.

## Build and verification

From the `ReasBook` directory on branch `v4.32.0`:

```bash
lake lean Papers/DFP_wolfe_local/Paper.lean
lake env lean Papers/DFP_wolfe_local/Paper.lean
```

`lake lean` checks the root and prepares its imported modules. The direct
`lake env lean` command rechecks the root against those artifacts. Validation
is restricted to this paper; the repository-wide build, generated documentation,
and comparator are not included in these commands.

For this refactor, the paper root passed, and all 32 declarations linked from
the paper-numbered navigation were audited with `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound` occur. Source scans found no `sorry`,
`admit`, or project-defined axioms. No diagnostic `#check`/`#print` commands
remain in `ReasLib`; the eleven paper navigation files intentionally retain
32 `#check` links. Comparator was not rerun for this update.

Resource validation includes eleven Python tests, all 2,565 declaration line
anchors, all 447 documented source hashes, and desktop/mobile browser checks
of the eleven paper statements, 32 exact code blocks, eight Verso sections,
paper landing page, and Verso-to-API declaration jumps. Re-run the Python checks
with:

```bash
python3 -m unittest discover -s ReasBook/Papers/DFP_wolfe_local/tools -p 'test_*.py'
```

`Paper.lean` imports the complete public `DFPWolfe` surface. The project uses
the Apache License, Version 2.0, consistent with the source development
repository.
