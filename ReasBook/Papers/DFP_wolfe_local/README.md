# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Venue:** arXiv:2608.21708v1 (`math.OC`), 2026
- **Paper ID:** `DFP_wolfe_local`
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1)
- **Source development:** [imathwy/DFP_wolfe_local](https://github.com/imathwy/DFP_wolfe_local)
- **Source snapshot:** [`75ba9f9aa9a190e23900503a5e9af6a377bddf6d`](https://github.com/imathwy/DFP_wolfe_local/commit/75ba9f9aa9a190e23900503a5e9af6a377bddf6d)

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
experiments and manuscript presentation files are maintained in the source
development repository and are not part of this ReasBook Lean contribution.
The implementation roots remain under this project directory while dedicated
Lake libraries preserve their public `DFPWolfe` and `ReasLib` module names.

## Statistics

The counts below cover the project's tracked Lean source files, including the
`DFPWolfe` and `ReasLib` implementation roots, their aggregate roots, and the
`Paper.lean` wrapper.

- **Lean code:** 829 `.lean` files, 159,827 physical lines, 149,306 nonblank lines
- **Declarations:** 4,887 (theorem/lemma/example: 4,112; other: 775)
- **Declaration breakdown:** 3,728 theorems, 384 lemmas, 669 definitions,
  14 abbreviations, 87 structures, and 5 instances
- **Module split:** 205 `DFPWolfe` files and 621 `ReasLib` files
- **Proof completion:** 4,112 / 4,112 theorem and lemma declarations have no placeholders
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
22 dependency edges, mathematical summaries, and expandable Lean source links.

Numbering follows the September 2026 `main-new-modify.tex` revision, not the
older numbered labels in some Lean docstrings. Each paper node groups reviewed
Lean proof components; some nodes correspond to several separate declarations
or only the specified parts of a result. The node's correspondence panel states
that scope explicitly. Edges are paths in the compiled declaration graph after
unassigned helpers are contracted, not manually inferred paper citations.
The grouping lives in [paper_results.json](tools/paper_results.json), and
[paper-data.json](theorem-map/paper-data.json) retains an explicit declaration
path witnessing each edge. Main-result summaries are reading aids; the linked
Lean statements give the exact formal hypotheses and conclusions.

To regenerate just the numbered view from the existing graph, run:

```bash
python3 ReasBook/Papers/DFP_wolfe_local/tools/generate_paper_graph.py
```

Optionally pass `--manuscript /path/to/main-new-modify.tex` to check all eleven
environment types, numbers, and TeX labels against the local manuscript. The
manuscript is not copied into this repository. Full graph regeneration also
regenerates this numbered projection and preserves the view switch.

The [interactive theorem map](theorem-map/index.html) and its
[machine-readable graph](theorem-map/data.json) cover the latest formalization
at ReasBook commit `1a74e5e51ee05415c98410f9052ba371ec546b43` on `v4.32.0`.
The map includes all 3,402 public source-declared theorems and lemmas:
2,271 have dependencies extracted from the compiled `DFP_wolfe_local.Paper`
environment, and 1,131 appear as source-only inventory entries. There are
6,624 distinct directed dependency edges. The source-only entries belong to
modules outside that aggregate root and have no inferred edges; the map does
not present their missing dependency evidence as independence.

The main-results group includes planar weak/strong Wolfe convergence, general
secant degeneration, sharp one-half Hölder regularity, and identity
initialization. Statement dependencies and proof dependencies are distinguished.
Definitions, private helpers, and compiler-generated declarations are contracted
using the ReasBook theorem graph SDK. Mathlib dependencies are outside this
project graph. Source links point to exact declaration lines in the immutable
source commit. Older docstrings retain their original labels; graph identities
use Lean declaration names rather than assigning new manuscript numbers.

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
  --evidence /tmp/dfp-theorem-map-evidence-new
```

Both output paths must be new. The evidence directory retains raw exported
declarations, an extraction log, and checksums. It is intentionally not committed.
The adapter includes the `DFPWolfe` and `ReasLib` module roots and handles the
Lean 4.32.0 extractor configuration explicitly. It uses one Lean thread and an
8 GiB Lean allocator limit; imported memory-mapped files can add to process RSS.
For rendering-only changes, `--reuse-evidence` accepts an existing evidence
directory after checking its source, extractor, and raw-data hashes.

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

`Paper.lean` imports the complete public `DFPWolfe` surface. The project uses
the Apache License, Version 2.0, consistent with the source development
repository.
