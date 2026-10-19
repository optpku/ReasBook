# The multiplier step size of two-block ADMM: convergence and counterexamples

- **Authors:** Not provided in the supplied manuscript.
- **Year:** 2026.
- **Contributor:** Qiming Dai ([@newbiedqm](https://github.com/newbiedqm)).
- **Project ID:** `glowinski_admm_counterexample`.
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`.
- **Mathlib:** `v4.32.0`, pinned by the repository's `lake-manifest.json`.
- **Paper link:** An arXiv link will be added when publicly available.

## Coverage

The development formalizes the corresponding mathematical results of the
supplied 2026 manuscript:

- convergence of exact two-block ADMM for multiplier factors up to `377/200`;
- image reduction and finite-memory Lyapunov certificates;
- fixed-polytope periodic counterexamples and uniform convergence endpoint bounds;
- one-block strictification and smooth strongly convex realization; and
- finite convex piecewise-quadratic objectives with periodic or geometrically
  growing trajectories.

All 11 named mathematical results in the manuscript have proved interfaces,
including the proposition with TeX label `prop:finite` that was missing from the
original JSON extraction. All 29 original JSON interfaces are verified. These
29 interfaces include definitions, overlapping items, and truncated extractions;
they are not 29 distinct manuscript theorems. Bibliographic discussion,
numerical experiments, and external computational software are outside the
formal theorem assertions.

The manuscript's TeX, PDF, and bibliography are not distributed with this source
contribution. The author field records the information available in the supplied
manuscript; it does not identify the formalization contributor as the paper author.

## Layout

`Paper.lean` imports the complete paper-facing surface and the reusable public
library. `GlowinskiADMM/` contains the original JSON-facing interfaces and the
additional finite-objectives proposition. `ReasLib/` contains the convergence,
interpolation, and exact rational certificate proofs.

All module paths start with `glowinski_admm_counterexample`, for example
`glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence`. This
avoids the DFP project's separate `ReasLib` module root. Public mathematical
declaration names remain unchanged, including the `ADMM` and `ConsensusADMM`
namespaces. Relocation changes import paths only; proof bodies and numeric
certificate data are preserved.

## Statistics and completion

- **Lean source:** 496 `.lean` files, 123,376 physical lines, including `Paper.lean`.
- **Proof completion:** 11 / 11 = 100% for the named manuscript results.
- **Verified JSON interfaces:** 29 / 29 = 100%.
- **Remaining placeholders:** `sorry`: 0; `admit`: 0.
- **Project-defined axioms:** 0.
- **Compiled public root:** 45,505 declarations (theorem constants: 41,936; other: 3,569).

Compiled declaration counts are reported separately from the manuscript result
counts, since exact numeric certificates generate many auxiliary declarations.

## Build and validation

From the repository's Lean project directory:

```bash
cd ReasBook
lake build glowinski_admm_counterexample
lake env lean Papers/glowinski_admm_counterexample/Paper.lean
```

The dedicated library checks this project, including its retained helper
modules. It does not request a repository-wide build. Build caches, compiled
artifacts, local verification logs, and generated review ZIP files are not part
of the source contribution.

The dedicated library build and the direct `Paper.lean` check passed on the
branch-pinned toolchain. A fresh whole-library audit checked 47,248 declarations and found only
`propext`, `Classical.choice`, and `Quot.sound`.

## Reading resources

[Docs](https://optpku.github.io/ReasBook/sites/glowinski_admm_counterexample/docs/) ·
[Verso](https://optpku.github.io/ReasBook/sites/glowinski_admm_counterexample/pages/) ·
[Theorem map](https://optpku.github.io/ReasBook/theorem-maps/papers/glowinski_admm_counterexample/)

The map groups the 30 imported public interface modules into 26 nodes. Interfaces
that expose the same primary compiled constant share a node; their alternative
labels and source files remain recorded in `data.json`. The 92 dependency edges
come from the compiled statement/proof dependencies of all checked constants,
with intermediate helper declarations and numeric certificates contracted.
This is a map of the public interfaces, rather than a count of distinct paper
theorems. The natural-language statements are copied from the interface source
comments.

To regenerate the checked map, export `glowinski_admm_counterexample.Paper`
with the theorem-graph SDK's `resources/Extract.lean` (set `rootModules` to `[]`
in its project JSON), then run:

```bash
python tools/generate_theorem_map.py --raw /path/to/export.json \
  --commit SOURCE_COMMIT --output theorem-map
```

Run the script from the project directory with `sdk/theorem_graph/src` and
`sdk/common/src` on `PYTHONPATH`. The export contains 45,505 declarations and is
kept outside the source repository. The map records its SHA-256 digest.
