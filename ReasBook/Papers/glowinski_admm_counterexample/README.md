# The multiplier step size of two-block ADMM: convergence and counterexamples

This is a catalog link folder on `main`; the complete Lean formalization is
kept on the `v4.32.0` version branch.

- **Authors:** Not provided in the supplied manuscript.
- **Year:** 2026
- **Contributor:** Qiming Dai ([@newbiedqm](https://github.com/newbiedqm))
- **Project ID:** `glowinski_admm_counterexample`
- **Lean/mathlib:** `v4.32.0` (`leanprover/lean4:v4.32.0`)
- **License:** Apache License, Version 2.0

**[Open the source on `v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/)**

[Paper.lean](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/Paper.lean) ·
[Source README](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/README.md)

## Coverage

The formalization covers convergence of exact two-block ADMM for multiplier
factors up to `377/200`, image reduction and finite-memory Lyapunov certificates,
fixed-polytope periodic counterexamples, strictification, smooth strongly convex
realization, and finite convex piecewise-quadratic objectives with periodic or
geometrically growing trajectories.

All 11 named manuscript results and all 29 original JSON interfaces are
verified. The JSON interfaces include overlapping items and definitions; they
are not 29 distinct manuscript theorems. Bibliographic discussion, numerical
experiments, and external computational software are outside the formal theorem
assertions.

## Source statistics and validation

- **Lean source:** 496 `.lean` files, 123,376 physical lines.
- **Compiled public root:** 45,505 declarations (theorem constants: 41,936; other: 3,569), including numeric-certificate auxiliaries.
- **Proof completion:** 11 / 11 = 100% of named manuscript results.
- **Remaining placeholders:** `sorry`: 0; `admit`: 0.
- **Project-defined axioms:** 0.

The dedicated library build and direct `Paper.lean` check passed on the pinned
toolchain. The version-branch source README records the validation commands and
full coverage details.

## Documentation

[API documentation](https://optpku.github.io/ReasBook/sites/glowinski_admm_counterexample/docs/) ·
[Verso reading pages](https://optpku.github.io/ReasBook/sites/glowinski_admm_counterexample/pages/) ·
[Theorem dependency map](https://optpku.github.io/ReasBook/theorem-maps/papers/glowinski_admm_counterexample/)

The documentation covers the 480 reachable public API modules. The Verso guide
links the public manuscript interfaces, and the theorem map provides 26 nodes
and 92 dependencies among the 30 overlapping public interfaces. An arXiv link
will be added when the manuscript is publicly available.
